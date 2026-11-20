import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PColAntiA
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PColAntiC

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ColumnAntisymmetry

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ}

def Q (L : TV n M (Fin m) →ₗ[ℂ] ℂ) (σ : Equiv.Perm (Fin m)) : Prop :=
  L ∘ₗ pm σ = ((Equiv.Perm.sign σ : ℤ) : ℂ) • L

/- English proof (translation)
Unfold `Q at *`. Rewrite using `[pm_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h1, LinearMap.smul_comp, h2, smul_smul, Equiv.Perm.sign_mul]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem Q_mul (L : TV n M (Fin m) →ₗ[ℂ] ℂ) {σ τ : Equiv.Perm (Fin m)} (h1 : Q L σ) (h2 : Q L τ) :
    Q L (σ * τ) := by
  unfold Q at *
  rw [pm_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h1, LinearMap.smul_comp, h2, smul_smul,
    Equiv.Perm.sign_mul]
  push_cast
  ring_nf

/- English proof (translation)
Unfold `Q`. Simplify using `[Module.End.one_eq_id]`.
-/
theorem Q_one (L : TV n M (Fin m) →ₗ[ℂ] ℂ) : Q L 1 := by
  unfold Q
  simp [Module.End.one_eq_id]

/- English proof (translation)
Unfold `Q`. Rewrite using `[Equiv.Perm.sign_swap h]`. Simplify using the standard rewrite rules.
-/
theorem Q_swap_iff (L : TV n M (Fin m) →ₗ[ℂ] ℂ) {p q : Fin m} (h : p ≠ q) :
    Q L (Equiv.swap p q) ↔ L ∘ₗ pm (Equiv.swap p q) = -L := by
  unfold Q
  rw [Equiv.Perm.sign_swap h]
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pm_top (σ : Equiv.Perm (Fin m)) (top : Fin n) (g : TV n M (Fin m)) :
    pm σ g (fun _ => top) = g (fun _ => top) := rfl

/- English proof (translation)
Establish `hne : i ≠ j` using `by intro h; rw [h] at hij; omega`. Rewrite using `[Q_swap_iff _ hne]`. Take `⟨R, hD, hR⟩` from `split E col hmono hc hP i j hij hcol`. Use `set P : Module.End ℂ (TV n M (Fin m)) := pm (Equiv.swap i j) with hPdef`. Establish `hx` using `(hP i j hij).1`.

Establish `PP : P * P = 1` using `by rw [hPdef, ← pm_mul, Equiv.swap_mul_self, pm_one]`. Establish `h2 : xJ E i * P = P * xJ E j - 1`. Combine the equalities or inequalities in the displayed calculation. Establish `hTP : (xJ E i - xJ E j + 1) * P = P * (1 + 1 - (xJ E i - xJ E j + 1)) - (1 + 1)`. Combine the equalities or inequalities in the displayed calculation.

Establish `key : colD E col * P = P * (R + R - colD E col) - (R + R)`. Rewrite using `[hD]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, hR, ← mul_assoc]`. Use `_ = (P * (1 + 1 - (xJ E i - xJ E j + 1)) - (1 + 1)) * R := by rw [hTP]`.

Use `_ = _ := by noncomm_ring`. Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Establish `e : colD E col (P f) = (colD E col * P) f` using `rfl`. Simplify using `only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.proj_apply]`. Rewrite using `[e, key]`.

Simplify using `only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, Pi.sub_apply, Pi.add_apply, pm_top, map_sub, map_add]`. Simplify using `only [hPdef, pm_top]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem Q_adj (E : Fin n → Fin n → Module.End ℂ M) (ℓ : M →ₗ[ℂ] ℂ) (top : Fin n) (col : Fin m → ℕ)
    (hmono : Monotone col) (hc : ∀ i j : Fin m, Commute (xJ E i) (xJ E j))
    (hP : ∀ i j : Fin m, (i : ℕ) + 1 = j →
      xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 ∧
      ∀ k : Fin m, k ≠ i → k ≠ j → Commute (xJ E k) (pm (Equiv.swap i j)))
    (i j : Fin m) (hij : (i : ℕ) + 1 = j) (hcol : col i = col j) :
    Q (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ colD E col) (Equiv.swap i j) := by
  have hne : i ≠ j := by intro h; rw [h] at hij; omega
  rw [Q_swap_iff _ hne]
  obtain ⟨R, hD, hR⟩ := split E col hmono hc hP i j hij hcol
  set P : Module.End ℂ (TV n M (Fin m)) := pm (Equiv.swap i j) with hPdef
  have hx := (hP i j hij).1
  have PP : P * P = 1 := by rw [hPdef, ← pm_mul, Equiv.swap_mul_self, pm_one]
  have h2 : xJ E i * P = P * xJ E j - 1 := by
    calc xJ E i * P = (P * P) * xJ E i * P := by rw [PP, one_mul]
      _ = P * (P * xJ E i + 1) * P - P * P := by noncomm_ring
      _ = P * (xJ E j * P) * P - 1 := by rw [← hx, PP]
      _ = P * xJ E j - 1 := by rw [mul_assoc, mul_assoc, PP, mul_one]
  have hTP : (xJ E i - xJ E j + 1) * P = P * (1 + 1 - (xJ E i - xJ E j + 1)) - (1 + 1) := by
    calc (xJ E i - xJ E j + 1) * P = xJ E i * P - xJ E j * P + P := by noncomm_ring
      _ = (P * xJ E j - 1) - (P * xJ E i + 1) + P := by rw [h2, hx]
      _ = _ := by noncomm_ring
  have key : colD E col * P = P * (R + R - colD E col) - (R + R) := by
    rw [hD]
    calc (xJ E i - xJ E j + 1) * R * P = (xJ E i - xJ E j + 1) * P * R := by
          rw [mul_assoc, hR, ← mul_assoc]
      _ = (P * (1 + 1 - (xJ E i - xJ E j + 1)) - (1 + 1)) * R := by rw [hTP]
      _ = _ := by noncomm_ring
  refine LinearMap.ext fun f => ?_
  have e : colD E col (P f) = (colD E col * P) f := rfl
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.proj_apply]
  rw [e, key]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, Pi.sub_apply, Pi.add_apply,
    pm_top, map_sub, map_add]
  simp only [hPdef, pm_top]
  ring

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro p q h hc; exact hadj p q (by omega) hc`. Consider the case `succ d ih`. Introduce `p q h hc`.

Set `r : Fin m` to `⟨(q : ℕ) - 1, by omega⟩`. Establish `hpr : col p = col r` using `le_antisymm (hmono (show p ≤ r from Fin.le_def.mpr (by simp [r]; omega))) (hc ▸ hmono (show r ≤ q from Fin.le_def.mpr (by simp [r])))`. Establish `hrq : col r = col q` using `hpr ▸ hc`. Establish `h1 : p ≠ r` using `fun e => by rw [Fin.ext_iff] at e; simp [r] at e; omega`. Establish `h2 : p ≠ q` using `fun e => by rw [Fin.ext_iff] at e; omega`.

Establish `hs : Equiv.swap p q = Equiv.swap r q * Equiv.swap p r * Equiv.swap r q`. Rewrite using `[Equiv.swap_mul_swap_mul_swap h1 h2, Equiv.swap_comm]`. Rewrite using `[hs]`. Establish `A` using `hadj r q (by simp [r]; omega) hrq`. Conclude with `Q_mul L (Q_mul L A (ih p r (by simp [r]; omega) hpr)) A`.
-/
theorem Q_lt (L : TV n M (Fin m) →ₗ[ℂ] ℂ) (col : Fin m → ℕ) (hmono : Monotone col)
    (hadj : ∀ i j : Fin m, (i : ℕ) + 1 = j → col i = col j → Q L (Equiv.swap i j)) :
    ∀ d (p q : Fin m), (q : ℕ) = p + d + 1 → col p = col q → Q L (Equiv.swap p q) := by
  intro d
  induction d with
  | zero => intro p q h hc; exact hadj p q (by omega) hc
  | succ d ih =>
    intro p q h hc
    let r : Fin m := ⟨(q : ℕ) - 1, by omega⟩
    have hpr : col p = col r := le_antisymm (hmono (show p ≤ r from Fin.le_def.mpr (by simp [r]; omega)))
      (hc ▸ hmono (show r ≤ q from Fin.le_def.mpr (by simp [r])))
    have hrq : col r = col q := hpr ▸ hc
    have h1 : p ≠ r := fun e => by rw [Fin.ext_iff] at e; simp [r] at e; omega
    have h2 : p ≠ q := fun e => by rw [Fin.ext_iff] at e; omega
    have hs : Equiv.swap p q = Equiv.swap r q * Equiv.swap p r * Equiv.swap r q := by
      rw [Equiv.swap_mul_swap_mul_swap h1 h2, Equiv.swap_comm]
    rw [hs]
    have A := hadj r q (by simp [r]; omega) hrq
    exact Q_mul L (Q_mul L A (ih p r (by simp [r]; omega) hpr)) A

/- English proof (translation)
Introduce `σ hσ`. Proceed by induction on `h : σ.support.card using Nat.strong_induction_on generalizing σ with`. Consider the case `_ k ih`. Distinguish the cases in `h1 : σ = 1`. Rewrite using `[h1]`.

Conclude with `Q_one L`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, σ x ≠ x := by`. Assume the negation of the conclusion as `hh`. Use `push Not at hh`. Conclude with `h1 (Equiv.ext hh)`.

Establish `hmem : ∀ p, col (σ p) = col p` using `by simpa [colG] using hσ`. Establish `hτ : Equiv.swap x (σ x) * σ ∈ colG col`. Simplify using `only [colG, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply]`. Introduce `p`. Rewrite using `[Equiv.swap_apply_def]`.

Use `split_ifs with e1 e2`. Rewrite using `[hmem x, ← e1, hmem]`. Rewrite using `[← hmem x, ← e2, hmem]`. Conclude with `hmem p`. Establish `hlt` using `Equiv.Perm.card_support_swap_mul hx`.

Establish `hq` using `ih _ (h ▸ hlt) _ hτ rfl`. Establish `hs` using `hsw x (σ x) hx.symm (hmem x).symm`. Use `Q_mul L hs hq` as an intermediate fact. Rewrite `this` using `[← mul_assoc, Equiv.swap_mul_self, one_mul]`. Then use the resulting hypothesis.
-/
theorem Q_colG (L : TV n M (Fin m) →ₗ[ℂ] ℂ) (col : Fin m → ℕ)
    (hsw : ∀ p q : Fin m, p ≠ q → col p = col q → Q L (Equiv.swap p q)) :
    ∀ σ ∈ colG col, Q L σ := by
  intro σ hσ
  induction h : σ.support.card using Nat.strong_induction_on generalizing σ with
  | _ k ih =>
    by_cases h1 : σ = 1
    · rw [h1]; exact Q_one L
    · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
        by_contra hh; push Not at hh; exact h1 (Equiv.ext hh)
      have hmem : ∀ p, col (σ p) = col p := by simpa [colG] using hσ
      have hτ : Equiv.swap x (σ x) * σ ∈ colG col := by
        simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply]
        intro p
        rw [Equiv.swap_apply_def]
        split_ifs with e1 e2
        · rw [hmem x, ← e1, hmem]
        · rw [← hmem x, ← e2, hmem]
        · exact hmem p
      have hlt := Equiv.Perm.card_support_swap_mul hx
      have hq := ih _ (h ▸ hlt) _ hτ rfl
      have hs := hsw x (σ x) hx.symm (hmem x).symm
      have := Q_mul L hs hq
      rwa [← mul_assoc, Equiv.swap_mul_self, one_mul] at this

/- English proof (translation)
Use function extensionality and compare the values at `J`. Simplify using `only [pm_apply, Pi.single_apply]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `rfl`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Introduce and unpack `rfl`. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules.
-/
theorem pm_single (σ : Equiv.Perm (Fin m)) (I : Fin m → Fin n) (v : M) :
    pm σ (Pi.single I v : TV n M (Fin m)) = Pi.single (I ∘ ⇑σ⁻¹) v := by
  funext J
  simp only [pm_apply, Pi.single_apply]
  congr 1
  apply propext
  constructor
  · rintro rfl; funext x; simp
  · rintro rfl; funext x; simp

end ColumnAntisymmetry

open ColumnAntisymmetry in
/- English proof (translation)
Introduce `_ hJM hH n M _ _ E hE ℓ hWh top htop m col b hmono hb`. Take `⟨hc, hP, _⟩` from `hJM n M E hE m`. Take `⟨hH1, _, _⟩` from `hH n M E hE ℓ hWh top htop`. Establish `hdeg` using `hH1 (Fin m) (npairs col) (colD E col) (deg_colD E col)`. Use `set L : TV n M (Fin m) →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ colD E col with hL`.

Establish `hLs : ∀ I v, L (Pi.single I v) = ℓ (colD E col (Pi.single I v) fun _ => top)` using `fun _ _ => rfl`. Establish `hsw : ∀ p q : Fin m, p ≠ q → col p = col q → Q L (Equiv.swap p q)`. Establish `hadj` using `fun i j hij hcol => Q_adj E ℓ top col hmono hc hP i j hij hcol`. Introduce `p q hpq hcol`. Break down `lt_or_gt_of_ne hpq with h | h` into its components or cases.

Conclude with `Q_lt L col hmono hadj ((q : ℕ) - p - 1) p q (by omega) hcol`. Rewrite using `[Equiv.swap_comm]`. Conclude with `Q_lt L col hmono hadj ((p : ℕ) - q - 1) q p (by omega) hcol.symm`. Establish `hQ` using `Q_colG L col hsw`. Establish `hbinj : ColInj col b` using `hb.1`.

Choose the witnesses or unpack the hypotheses as in `⟨c, hcb⟩ : ∃ c : ℂ, ∀ v, L (Pi.single b v) = c * ℓ v := by`. Break down `(npairs_le col top htop b hbinj).lt_or_eq with hlt | heq` into its components or cases. Conclude with `⟨0, fun v => by rw [hLs, (hdeg b).1 hlt v]; simp⟩`. Take `⟨c, hc⟩` from `(hdeg b).2 heq`. Conclude with `⟨c, fun v => by rw [hLs, hc v]⟩`.

Establish `hmemG : ∀ σ ∈ colG col, ∀ p, col (σ p) = col p` using `fun σ hσ => by simpa [colG] using hσ`. Establish `hval : ∀ σ ∈ colG col, ∀ v, L (Pi.single (b ∘ σ) v) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * (c * ℓ v)`. Introduce `σ hσ v`. Establish `hσ' : σ⁻¹ ∈ colG col`. Simplify using `only [colG, Finset.mem_filter, Finset.mem_univ, true_and]`.

Introduce `p`. Use `hmemG σ hσ (σ⁻¹ p)` as an intermediate fact. Simplify using `at this`. Conclude with `this.symm`. Establish `e : (Pi.single (b ∘ σ) v : TV n M (Fin m)) = pm σ⁻¹ (Pi.single b v)`.

Rewrite using `[pm_single, inv_inv]`. Rewrite using `[e, ← LinearMap.comp_apply, hQ _ hσ', LinearMap.smul_apply, hcb, Equiv.Perm.sign_inv, smul_eq_mul]`. Establish `hzero : ∀ I : Fin m → Fin n, I ∉ (colG col).image (fun σ : Equiv.Perm (Fin m) => b ∘ ⇑σ) → ∀ v, L (Pi.single I v) = 0`. Introduce `I hI v`. Distinguish the cases in `hinj : ColInj col I`.

Establish `hle` using `npairs_le col top htop I hinj`. Break down `hle.lt_or_eq with hlt | heq` into its components or cases. Rewrite using `[hLs, (hdeg I).1 hlt v]`. It suffices to derive a contradiction. Take `⟨σ, hσ, e⟩` from `eq_of_le col top htop b I hb hinj heq.ge`.

Conclude with `hI (Finset.mem_image.mpr ⟨σ, hσ, e.symm⟩)`. Simplify using `only [ColInj, not_forall] at hinj`. Take `⟨p, q, hcol, hIpq, hpq⟩` from `hinj`. Establish `hfix : (Pi.single I v : TV n M (Fin m)) = pm (Equiv.swap p q) (Pi.single I v)`. Rewrite using `[pm_single, Equiv.swap_inv]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, Equiv.swap_apply_def]`. Use `split_ifs with h1 h2`. Rewrite using `[h1, hIpq]`.

Rewrite using `[h2, hIpq]`. Both sides reduce to the same expression. Establish `h` using `(Q_swap_iff L hpq).mp (hsw p q hpq hcol)`. Establish `h2 : L (Pi.single I v) = -L (Pi.single I v)` using `by conv_lhs => rw [hfix]`. Rewrite using `[← LinearMap.comp_apply, h, LinearMap.neg_apply]`.

Establish `h3 : (2 : ℂ) * L (Pi.single I v) = 0` using `by linear_combination h2`. Simplify using `using h3`. Use `⟨c, LinearMap.ext fun f => ?_⟩` and prove the remaining obligations. Use `show L f = c * ℓ (cA col b f)`. Rewrite using `[cA_apply, alt_apply, map_sum]`.

Use `conv_lhs => rw [← Finset.univ_sum_single f, map_sum]`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ ((colG col).image (fun σ : Equiv.Perm (Fin m) => b ∘ ⇑σ))) (fun I _ hI => hzero I hI (f I))]`. Rewrite using `[Finset.sum_image]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ hσ => ?_` and prove the remaining obligations.

Rewrite using `[hval σ hσ, map_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Introduce `σ hσ τ hτ e`. Use `Equiv.ext fun p => hb.1 _ _ ?_ (congrFun e p)` and prove the remaining obligations. Rewrite using `[hmemG σ hσ, hmemG τ hτ]`.
-/
theorem colAnti_of : TensorGl → JMComm → Height → ColAnti := by
  intro _ hJM hH n M _ _ E hE ℓ hWh top htop m col b hmono hb
  obtain ⟨hc, hP, _⟩ := hJM n M E hE m
  obtain ⟨hH1, _, _⟩ := hH n M E hE ℓ hWh top htop
  have hdeg := hH1 (Fin m) (npairs col) (colD E col) (deg_colD E col)
  set L : TV n M (Fin m) →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ colD E col with hL
  have hLs : ∀ I v, L (Pi.single I v) = ℓ (colD E col (Pi.single I v) fun _ => top) := fun _ _ => rfl
  have hsw : ∀ p q : Fin m, p ≠ q → col p = col q → Q L (Equiv.swap p q) := by
    have hadj := fun i j hij hcol => Q_adj E ℓ top col hmono hc hP i j hij hcol
    intro p q hpq hcol
    rcases lt_or_gt_of_ne hpq with h | h
    · exact Q_lt L col hmono hadj ((q : ℕ) - p - 1) p q (by omega) hcol
    · rw [Equiv.swap_comm]
      exact Q_lt L col hmono hadj ((p : ℕ) - q - 1) q p (by omega) hcol.symm
  have hQ := Q_colG L col hsw
  have hbinj : ColInj col b := hb.1
  obtain ⟨c, hcb⟩ : ∃ c : ℂ, ∀ v, L (Pi.single b v) = c * ℓ v := by
    rcases (npairs_le col top htop b hbinj).lt_or_eq with hlt | heq
    · exact ⟨0, fun v => by rw [hLs, (hdeg b).1 hlt v]; simp⟩
    · obtain ⟨c, hc⟩ := (hdeg b).2 heq
      exact ⟨c, fun v => by rw [hLs, hc v]⟩
  have hmemG : ∀ σ ∈ colG col, ∀ p, col (σ p) = col p := fun σ hσ => by simpa [colG] using hσ
  have hval : ∀ σ ∈ colG col, ∀ v, L (Pi.single (b ∘ σ) v) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * (c * ℓ v) := by
    intro σ hσ v
    have hσ' : σ⁻¹ ∈ colG col := by
      simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and]
      intro p
      have := hmemG σ hσ (σ⁻¹ p)
      simp at this
      exact this.symm
    have e : (Pi.single (b ∘ σ) v : TV n M (Fin m)) = pm σ⁻¹ (Pi.single b v) := by
      rw [pm_single, inv_inv]
    rw [e, ← LinearMap.comp_apply, hQ _ hσ', LinearMap.smul_apply, hcb, Equiv.Perm.sign_inv, smul_eq_mul]
  have hzero : ∀ I : Fin m → Fin n, I ∉ (colG col).image (fun σ : Equiv.Perm (Fin m) => b ∘ ⇑σ) → ∀ v, L (Pi.single I v) = 0 := by
    intro I hI v
    by_cases hinj : ColInj col I
    · have hle := npairs_le col top htop I hinj
      rcases hle.lt_or_eq with hlt | heq
      · rw [hLs, (hdeg I).1 hlt v]
      · exfalso
        obtain ⟨σ, hσ, e⟩ := eq_of_le col top htop b I hb hinj heq.ge
        exact hI (Finset.mem_image.mpr ⟨σ, hσ, e.symm⟩)
    · simp only [ColInj, not_forall] at hinj
      obtain ⟨p, q, hcol, hIpq, hpq⟩ := hinj
      have hfix : (Pi.single I v : TV n M (Fin m)) = pm (Equiv.swap p q) (Pi.single I v) := by
        rw [pm_single, Equiv.swap_inv]
        congr 1
        funext x
        simp only [Function.comp_apply, Equiv.swap_apply_def]
        split_ifs with h1 h2
        · rw [h1, hIpq]
        · rw [h2, hIpq]
        · rfl
      have h := (Q_swap_iff L hpq).mp (hsw p q hpq hcol)
      have h2 : L (Pi.single I v) = -L (Pi.single I v) := by
        conv_lhs => rw [hfix]
        rw [← LinearMap.comp_apply, h, LinearMap.neg_apply]
      have h3 : (2 : ℂ) * L (Pi.single I v) = 0 := by linear_combination h2
      simpa using h3
  refine ⟨c, LinearMap.ext fun f => ?_⟩
  show L f = c * ℓ (cA col b f)
  rw [cA_apply, alt_apply, map_sum]
  conv_lhs => rw [← Finset.univ_sum_single f, map_sum]
  rw [← Finset.sum_subset (Finset.subset_univ ((colG col).image (fun σ : Equiv.Perm (Fin m) => b ∘ ⇑σ)))
    (fun I _ hI => hzero I hI (f I))]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [hval σ hσ, map_smul, smul_eq_mul]
    ring
  · intro σ hσ τ hτ e
    refine Equiv.ext fun p => hb.1 _ _ ?_ (congrFun e p)
    rw [hmemG σ hσ, hmemG τ hτ]

end PositivityTheory.Rg.Cz

end
