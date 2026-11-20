import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffNmul
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NMulEndo

variable {R : Type} [CommRing R] {d : ℕ}

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero (by rintro (j | j); exacts [hu j, hv j])`.
-/
theorem hasSubst_elim {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j); exacts [hu j, hv j])

/- English proof (translation)
The claim follows from `constantCoeff_subst_eq_zero (hasSubst_elim hu hv) (by rintro (j | j); exacts [hu j, hv j]) (hμ i)`.
-/
theorem constantCoeff_op (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim hu hv) (by rintro (j | j); exacts [hu j, hv j]) (hμ i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [op, at2]`. Rewrite using `[subst_comp_subst_apply (hasSubst_elim hu hv) hw]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Apply the tactic sequence `rcases j with j | j <;> rfl`.
-/
theorem subst_op (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) {σ τ : Type}
    {u v : Fin d → MvPowerSeries σ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {w : σ → MvPowerSeries τ R} (hw : HasSubst w) :
    (fun i => subst w (op μ u v i)) = op μ (fun i => subst w (u i)) (fun i => subst w (v i)) := by
  funext i
  simp only [op, at2]
  rw [subst_comp_subst_apply (hasSubst_elim hu hv) hw]
  congr 1
  funext j
  rcases j with j | j <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hs : HasSubst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R)) (fun j => X (Sum.inl j)))` using `hasSubst_elim (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)`. Establish `hab` using `hasSubst_elim ha hb`. Establish `h` using `congrArg (subst (Sum.elim a b)) (hμ.comm i)`. Simplify using `only [swap, at2] at h`.

Rewrite `h` using `[subst_comp_subst_apply hs hab]`. Establish `e : (fun s => subst (Sum.elim a b) (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R)) (fun j => X (Sum.inl j)) s)) = Sum.elim b a`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `rcases s with s | s <;> simp [subst_X hab]`. Rewrite `h` using `[e]`.

Conclude with `h`.
-/
theorem op_comm {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) {τ : Type}
    {a b : Fin d → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    op μ b a = op μ a b := by
  funext i
  have hs : HasSubst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun j => X (Sum.inl j))) :=
    hasSubst_elim (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)
  have hab := hasSubst_elim ha hb
  have h := congrArg (subst (Sum.elim a b)) (hμ.comm i)
  simp only [swap, at2] at h
  rw [subst_comp_subst_apply hs hab] at h
  have e : (fun s => subst (Sum.elim a b) (Sum.elim (fun j => (X (Sum.inr j) :
      MvPowerSeries (Fin d ⊕ Fin d) R)) (fun j => X (Sum.inl j)) s)) = Sum.elim b a := by
    funext s
    rcases s with s | s <;> simp [subst_X hab]
  rw [e] at h
  exact h

/- English proof (translation)
Establish `hW : HasSubst (Sum.elim a (Sum.elim b c))` using `hasSubst_of_constantCoeff_zero (by rintro (j | j | j); exacts [ha j, hb j, hc j])`. Establish `h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0` using `fun _ => constantCoeff_X _`. Establish `h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0` using `fun _ => constantCoeff_X _`. Establish `h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0` using `fun _ => constantCoeff_X _`. Establish `h` using `congrArg (fun F : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R => fun i => subst (Sum.elim a (Sum.elim b c)) (F i)) hμ.assoc`.

Apply the tactic sequence `try simp only at h`. Rewrite `h` using `[subst_op μ (constantCoeff_op μ hμ.const h1 h2) h3 hW, subst_op μ h1 h2 hW, subst_op μ h1 (constantCoeff_op μ hμ.const h2 h3) hW, subst_op μ h2 h3 hW]`. Simplify `h` using `[x1, x2, x3, subst_X hW]`.
-/
theorem op_assoc {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) {τ : Type}
    {a b c : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (hc : ∀ i, constantCoeff (c i) = 0) :
    op μ (op μ a b) c = op μ a (op μ b c) := by
  have hW : HasSubst (Sum.elim a (Sum.elim b c)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j | j); exacts [ha j, hb j, hc j])
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have h := congrArg (fun F : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R =>
    fun i => subst (Sum.elim a (Sum.elim b c)) (F i)) hμ.assoc
  try simp only at h
  rw [subst_op μ (constantCoeff_op μ hμ.const h1 h2) h3 hW, subst_op μ h1 h2 hW,
    subst_op μ h1 (constantCoeff_op μ hμ.const h2 h3) hW, subst_op μ h2 h3 hW] at h
  simpa [x1, x2, x3, subst_X hW] using h

/- English proof (translation)
Rewrite using `[op_assoc hμ ha hb (constantCoeff_op μ hμ.const hc he), ← op_assoc hμ hb hc he, op_comm hμ hc hb, op_assoc hμ hc hb he, ← op_assoc hμ ha hc (constantCoeff_op μ hμ.const hb he)]`.
-/
theorem op_interchange {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) {τ : Type}
    {a b c e : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (hc : ∀ i, constantCoeff (c i) = 0)
    (he : ∀ i, constantCoeff (e i) = 0) :
    op μ (op μ a b) (op μ c e) = op μ (op μ a c) (op μ b e) := by
  rw [op_assoc hμ ha hb (constantCoeff_op μ hμ.const hc he), ← op_assoc hμ hb hc he,
    op_comm hμ hc hb, op_assoc hμ hc hb he,
    ← op_assoc hμ ha hc (constantCoeff_op μ hμ.const hb he)]

/- English proof (translation)
Establish `hw : HasSubst (fun _ : Fin d => (0 : MvPowerSeries τ R))` using `hasSubst_of_constantCoeff_zero fun _ => map_zero _`. Establish `hz : subst (fun _ : Fin d => (0 : MvPowerSeries τ R)) (0 : MvPowerSeries (Fin d) R) = 0`. Rewrite using `[← coe_substAlgHom hw, map_zero]`. Establish `h` using `congrArg (fun F : Fin d → MvPowerSeries (Fin d) R => fun i => subst (fun _ : Fin d => (0 : MvPowerSeries τ R)) (F i)) hμ.unit`. Apply the tactic sequence `try simp only at h`.

Rewrite `h` using `[subst_op μ (fun i => constantCoeff_X i) (fun _ => map_zero _) hw]`. Simplify `h` using `[subst_X hw, hz]`.
-/
theorem op_zero_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) (τ : Type) :
    op μ (fun _ => (0 : MvPowerSeries τ R)) (fun _ => 0) = fun _ => 0 := by
  have hw : HasSubst (fun _ : Fin d => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  have hz : subst (fun _ : Fin d => (0 : MvPowerSeries τ R)) (0 : MvPowerSeries (Fin d) R) = 0 := by
    rw [← coe_substAlgHom hw, map_zero]
  have h := congrArg (fun F : Fin d → MvPowerSeries (Fin d) R =>
    fun i => subst (fun _ : Fin d => (0 : MvPowerSeries τ R)) (F i)) hμ.unit
  try simp only at h
  rw [subst_op μ (fun i => constantCoeff_X i) (fun _ => map_zero _) hw] at h
  simpa [subst_X hw, hz] using h

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use `show subst a (0 : MvPowerSeries (Fin d) R) = 0`. Rewrite using `[← coe_substAlgHom (hasSubst_of_constantCoeff_zero ha), map_zero]`.
-/
theorem subst_nmul_zero {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {a : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0) :
    (fun j => subst a (nmul μ 0 j)) = fun _ => 0 := by
  funext j
  show subst a (0 : MvPowerSeries (Fin d) R) = 0
  rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero ha), map_zero]

/- English proof (translation)
Establish `hs` using `hasSubst_of_constantCoeff_zero ha`. Rewrite using `[QLogDefect.nmul_succ, subst_op μ (QLogDefect.constantCoeff_nmul hμ k) (fun i => constantCoeff_X i) hs]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `subst_X hs i`.
-/
theorem subst_nmul_succ {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {a : Fin d → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (k : ℕ) :
    (fun j => subst a (nmul μ (k + 1) j)) = op μ (fun j => subst a (nmul μ k j)) a := by
  have hs := hasSubst_of_constantCoeff_zero ha
  rw [QLogDefect.nmul_succ, subst_op μ (QLogDefect.constantCoeff_nmul hμ k)
    (fun i => constantCoeff_X i) hs]
  congr 1
  funext i
  exact subst_X hs i

/- English proof (translation)
The claim follows from `constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha (QLogDefect.constantCoeff_nmul hμ k j)`.
-/
theorem constantCoeff_subst_nmul {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {a : Fin d → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (k : ℕ) (j : Fin d) :
    constantCoeff (subst a (nmul μ k j)) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha
    (QLogDefect.constantCoeff_nmul hμ k j)

/- English proof (translation)
Establish `hab` using `constantCoeff_op μ hμ.const ha hb`. Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[subst_nmul_zero μ hab, subst_nmul_zero μ ha, subst_nmul_zero μ hb, op_zero_zero hμ]`. Consider the case `succ k ih`.

Rewrite using `[subst_nmul_succ μ hμ.const hab, ih, subst_nmul_succ μ hμ.const ha, subst_nmul_succ μ hμ.const hb, op_interchange hμ (constantCoeff_subst_nmul μ hμ.const ha k) (constantCoeff_subst_nmul μ hμ.const hb k) ha hb]`.
-/
theorem subst_nmul_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : IsLaw μ) (k : ℕ)
    {τ : Type} {a b : Fin d → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) :
    (fun j => subst (op μ a b) (nmul μ k j)) =
      op μ (fun j => subst a (nmul μ k j)) (fun j => subst b (nmul μ k j)) := by
  have hab := constantCoeff_op μ hμ.const ha hb
  induction k with
  | zero =>
    rw [subst_nmul_zero μ hab, subst_nmul_zero μ ha, subst_nmul_zero μ hb, op_zero_zero hμ]
  | succ k ih =>
    rw [subst_nmul_succ μ hμ.const hab, ih, subst_nmul_succ μ hμ.const ha,
      subst_nmul_succ μ hμ.const hb,
      op_interchange hμ (constantCoeff_subst_nmul μ hμ.const ha k)
        (constantCoeff_subst_nmul μ hμ.const hb k) ha hb]

/- English proof (translation)
Introduce `R _ d μ hμ k`. Use `⟨QLogDefect.constantCoeff_nmul hμ.const k, fun j => ?_⟩` and prove the remaining obligations. Establish `hL : ∀ i, constantCoeff ((fun i => X (Sum.inl i) : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) i) = 0` using `fun _ => constantCoeff_X _`. Establish `hR : ∀ i, constantCoeff ((fun i => X (Sum.inr i) : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) i) = 0` using `fun _ => constantCoeff_X _`. Establish `hxy : op μ (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) (fun i => X (Sum.inr i)) = μ`.

Use function extensionality and compare the values at `i`. Establish `e : (Sum.elim (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) (fun i => X (Sum.inr i))) = X`. Apply the tactic sequence `funext s; rcases s with s | s <;> rfl`. Use `show subst _ (μ i) = μ i`. Rewrite using `[e, subst_self]`.

Both sides reduce to the same expression. Establish `h` using `congrFun (subst_nmul_op hμ k hL hR) j`. Rewrite `h` using `[hxy]`. Conclude with `h`.
-/
theorem isHom_nmul : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ k : ℕ, IsHom μ μ (nmul μ k) := by
  intro R _ d μ hμ k
  refine ⟨QLogDefect.constantCoeff_nmul hμ.const k, fun j => ?_⟩
  have hL : ∀ i, constantCoeff ((fun i => X (Sum.inl i) : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have hR : ∀ i, constantCoeff ((fun i => X (Sum.inr i) : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) i) = 0 :=
    fun _ => constantCoeff_X _
  have hxy : op μ (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inr i)) = μ := by
    funext i
    have e : (Sum.elim (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (fun i => X (Sum.inr i))) = X := by
      funext s; rcases s with s | s <;> rfl
    show subst _ (μ i) = μ i
    rw [e, subst_self]; rfl
  have h := congrFun (subst_nmul_op hμ k hL hR) j
  rw [hxy] at h
  exact h

end GlobalTheory.NMulEndo
