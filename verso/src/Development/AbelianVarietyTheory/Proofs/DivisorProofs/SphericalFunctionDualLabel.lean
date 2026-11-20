import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms

noncomputable section

open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.InvTranspose

section Ring

variable {R : Type} [CommRing R] {n : ℕ}

def flipM (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := A.transpose.submatrix Fin.rev Fin.rev

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem flipM_apply (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) : flipM A i j = A j.rev i.rev := rfl

/- English proof (translation)
Unfold `flipM`. Rewrite using `[Matrix.transpose_mul]`. Conclude with `(Matrix.submatrix_mul_equiv _ _ _ (Fin.revPerm : Fin n ≃ Fin n) _).symm`.
-/
theorem flipM_mul (A B : Matrix (Fin n) (Fin n) R) : flipM (A * B) = flipM B * flipM A := by
  unfold flipM
  rw [Matrix.transpose_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ (Fin.revPerm : Fin n ≃ Fin n) _).symm

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[flipM_apply, Matrix.one_apply, eq_comm]`.
-/
theorem flipM_one : flipM (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  simp [flipM_apply, Matrix.one_apply, eq_comm]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[flipM_apply]`.
-/
theorem flipM_flipM (A : Matrix (Fin n) (Fin n) R) : flipM (flipM A) = A := by
  ext i j
  simp [flipM_apply]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[flipM_apply]`. Establish `h' : j.rev ≠ i.rev` using `fun e => h (Fin.rev_injective e).symm`.

Simplify using `[flipM_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h']`.
-/
theorem flipM_diagonal (a : Fin n → R) : flipM (Matrix.diagonal a) = Matrix.diagonal (fun i => a i.rev) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [flipM_apply]
  · have h' : j.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
    simp [flipM_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h']

def theta : GL (Fin n) R →* GL (Fin n) R where
  toFun g := ⟨flipM ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R), flipM (g : Matrix (Fin n) (Fin n) R),
    by rw [← flipM_mul, Units.mul_inv, flipM_one], by rw [← flipM_mul, Units.inv_mul, flipM_one]⟩
  map_one' := by
    apply Units.ext
    simp [flipM_one]
  map_mul' g h := by
    apply Units.ext
    simp only [mul_inv_rev, Units.val_mul, flipM_mul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_theta (g : GL (Fin n) R) :
    (theta g : Matrix (Fin n) (Fin n) R) = flipM ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[coe_theta]`. Conclude with `flipM_flipM _`.
-/
theorem theta_theta (g : GL (Fin n) R) : theta (theta g) = g := by
  apply Units.ext
  rw [coe_theta]
  exact flipM_flipM _

end Ring

section Field

variable {L : Type} [Field L] {n : ℕ}

/- English proof (translation)
Take `⟨k, rfl⟩` from `hg`. Use `⟨theta k, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[coe_theta, ← map_inv]`. Both sides reduce to the same expression.
-/
theorem theta_mem {O : Subring L} {g : GL (Fin n) L} (hg : g ∈ GLint (Fin n) O) : theta g ∈ GLint (Fin n) O := by
  obtain ⟨k, rfl⟩ := hg
  refine ⟨theta k, ?_⟩
  apply Units.ext
  rw [coe_theta, ← map_inv]
  rfl

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[coe_theta, flipM_apply]`. Conclude with `Formalism.UG.P.spherical_upper_inv b hb (Fin.rev_lt_rev.2 hij)`.
-/
theorem theta_upper {b : GL (Fin n) L} (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    ((theta b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := by
  intro i j hij
  rw [coe_theta, flipM_apply]
  exact Formalism.UG.P.spherical_upper_inv b hb (Fin.rev_lt_rev.2 hij)

/- English proof (translation)
Rewrite using `[coe_theta, flipM_apply, ← Formalism.UG.P.spherical_diag_mul _ _ (Formalism.UG.P.spherical_upper_inv b hb) hb, Units.inv_mul, Matrix.one_apply_eq]`.
-/
theorem theta_diag {b : GL (Fin n) L} (hb : (b : Matrix (Fin n) (Fin n) L).BlockTriangular id) (i : Fin n) :
    ((theta b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * (b : Matrix (Fin n) (Fin n) L) i.rev i.rev = 1 := by
  rw [coe_theta, flipM_apply, ← Formalism.UG.P.spherical_diag_mul _ _ (Formalism.UG.P.spherical_upper_inv b hb) hb,
    Units.inv_mul, Matrix.one_apply_eq]

/- English proof (translation)
Substitute `hd` using the available equality. Establish `h1 : i.1 < (dualLab d).length` using `by simp only [dualLab, List.length_reverse, List.length_map]; exact i.2`. Rewrite using `[List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.rev.2]`. Simplify using `only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]`. Use `congr 2`.

Use linear arithmetic over natural numbers and integers.
-/
theorem getD_dualLab' (d : List ℤ) (hd : d.length = n) (i : Fin n) :
    (dualLab d).getD i.1 0 = -(d.getD i.rev.1 0) := by
  subst hd
  have h1 : i.1 < (dualLab d).length := by simp only [dualLab, List.length_reverse, List.length_map]; exact i.2
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.rev.2]
  simp only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]
  congr 2
  omega

variable [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Take `⟨ϖ, hϖ, a, ha, b, hb, e⟩` from `h`. Establish `h0 : ϖ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hϖ` using `[map_zero]`. Conclude with `WithZero.zero_ne_coe hϖ`.

Set `D : GL (Fin n) L` to `⟨Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0), Matrix.diagonal (fun i : Fin n => ϖ ^ (-(d.getD i 0))), by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i`. Rewrite using `[← zpow_add₀ h0, add_neg_cancel, zpow_zero],`. Use `by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i`. Rewrite using `[← zpow_add₀ h0, neg_add_cancel, zpow_zero]⟩`. Establish `hg : g = a * D * b` using `Units.ext e`.

Use `⟨ϖ, hϖ, theta a, theta_mem ha, theta b, theta_mem hb, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, map_mul, map_mul, Units.val_mul, Units.val_mul]`. Use `congr 2`. Rewrite using `[coe_theta]`. Express the relevant statement in the definitionally equal form `flipM (Matrix.diagonal (fun i : Fin n => ϖ ^ (-(d.getD i 0)))) = _`.

Rewrite using `[flipM_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[getD_dualLab' d hd]`.
-/
theorem hasDiv_theta {O : Subring L} {d : List ℤ} (hd : d.length = n) {g : GL (Fin n) L} (h : HasDiv O d g) :
    HasDiv O (dualLab d) (theta g) := by
  obtain ⟨ϖ, hϖ, a, ha, b, hb, e⟩ := h
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  let D : GL (Fin n) L := ⟨Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0),
    Matrix.diagonal (fun i : Fin n => ϖ ^ (-(d.getD i 0))),
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i
       rw [← zpow_add₀ h0, add_neg_cancel, zpow_zero],
    by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i
       rw [← zpow_add₀ h0, neg_add_cancel, zpow_zero]⟩
  have hg : g = a * D * b := Units.ext e
  refine ⟨ϖ, hϖ, theta a, theta_mem ha, theta b, theta_mem hb, ?_⟩
  rw [hg, map_mul, map_mul, Units.val_mul, Units.val_mul]
  congr 2
  rw [coe_theta]
  change flipM (Matrix.diagonal (fun i : Fin n => ϖ ^ (-(d.getD i 0)))) = _
  rw [flipM_diagonal]
  congr 1
  funext i
  rw [getD_dualLab' d hd]

/- English proof (translation)
Establish `hdd : dualLab (dualLab d) = d` using `by simp [dualLab, List.map_reverse]`. Establish `: HasDiv O (dualLab d) g ↔ HasDiv O d (theta g)`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `hasDiv_theta (by simpa [dualLab] using hd) h` as an intermediate fact.

Rewrite `this` using `[hdd]`. Then use the resulting hypothesis. Introduce `h`. Use `hasDiv_theta hd h` as an intermediate fact. Rewrite `this` using `[theta_theta]`. Then use the resulting hypothesis. Unfold `divInd`.

Distinguish the cases in `h : HasDiv O d (theta g)`. Rewrite using `[Set.indicator_of_mem (s := {g | HasDiv O d g}) h, Set.indicator_of_mem (s := {g | HasDiv O (dualLab d) g}) (this.2 h)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (s := {g | HasDiv O d g}) h, Set.indicator_of_notMem (s := {g | HasDiv O (dualLab d) g}) (fun h' => h (this.1 h'))]`.
-/
theorem divInd_theta (O : Subring L) {d : List ℤ} (hd : d.length = n) (g : GL (Fin n) L) :
    divInd O (dualLab d) g = divInd O d (theta g) := by
  have hdd : dualLab (dualLab d) = d := by simp [dualLab, List.map_reverse]
  have : HasDiv O (dualLab d) g ↔ HasDiv O d (theta g) := by
    constructor
    · intro h
      have := hasDiv_theta (by simpa [dualLab] using hd) h
      rwa [hdd] at this
    · intro h
      have := hasDiv_theta hd h
      rwa [theta_theta] at this
  unfold divInd
  by_cases h : HasDiv O d (theta g)
  · rw [Set.indicator_of_mem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_mem (s := {g | HasDiv O (dualLab d) g}) (this.2 h)]
    rfl
  · rw [Set.indicator_of_notMem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_notMem (s := {g | HasDiv O (dualLab d) g}) (fun h' => h (this.1 h'))]

/- English proof (translation)
Take `⟨ϖ, hϖ, a, ha, b, hb, e⟩` from `h`. Use `⟨ϖ, hϖ, a, ha, b * k, mul_mem hb hk, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul, e]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem hasDiv_mul_right {O : Subring L} {d : List ℤ} {g k : GL (Fin n) L} (hk : k ∈ GLint (Fin n) O) (h : HasDiv O d g) :
    HasDiv O d (g * k) := by
  obtain ⟨ϖ, hϖ, a, ha, b, hb, e⟩ := h
  refine ⟨ϖ, hϖ, a, ha, b * k, mul_mem hb hk, ?_⟩
  rw [Units.val_mul, Units.val_mul, e]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Unfold `divInd`. Distinguish the cases in `h : HasDiv O d g`. Rewrite using `[Set.indicator_of_mem (s := {g | HasDiv O d g}) h, Set.indicator_of_mem (s := {g | HasDiv O d g}) (hasDiv_mul_right hk h)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (s := {g | HasDiv O d g}) h, Set.indicator_of_notMem (s := {g | HasDiv O d g})]`.

Introduce `h'`. Use `hasDiv_mul_right (inv_mem hk) h'` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_right]`. Conclude with `h this`.
-/
theorem divInd_mul_right (O : Subring L) (d : List ℤ) (g k : GL (Fin n) L) (hk : k ∈ GLint (Fin n) O) :
    divInd O d (g * k) = divInd O d g := by
  unfold divInd
  by_cases h : HasDiv O d g
  · rw [Set.indicator_of_mem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_mem (s := {g | HasDiv O d g}) (hasDiv_mul_right hk h)]
    rfl
  · rw [Set.indicator_of_notMem (s := {g | HasDiv O d g}) h,
      Set.indicator_of_notMem (s := {g | HasDiv O d g})]
    intro h'
    have := hasDiv_mul_right (inv_mem hk) h'
    rw [mul_inv_cancel_right] at this
    exact h this

end Field

/- English proof (translation)
Establish `hF' : ∀ g : G, F (QuotientGroup.mk (s` using `K) g).out = F g := fun g => by`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K g`. Rewrite using `[hk, hF _ _ k.2]`. Set `m : G ⧸ K → G ⧸ K` to `fun x => QuotientGroup.mk (t x.out)`. Establish `hm : Function.Involutive m` using `fun x => by`.

Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K (t x.out)`. Simplify using `only [m]`. Rewrite using `[hk, map_mul, ht, QuotientGroup.mk_mul_of_mem _ (hK _ k.2), QuotientGroup.out_eq']`. Rewrite using `[← finsum_comp_equiv (hm.toPerm m) (f := fun x : G ⧸ K => F x.out)]`. Conclude with `finsum_congr fun x => (hF' _).symm`.
-/
theorem finsum_out_involution {G : Type} [Group G] (K : Subgroup G) (t : G →* G) (ht : ∀ g, t (t g) = g)
    (hK : ∀ k ∈ K, t k ∈ K) (F : G → ℂ) (hF : ∀ g, ∀ k ∈ K, F (g * k) = F g) :
    ∑ᶠ x : G ⧸ K, F (t x.out) = ∑ᶠ x : G ⧸ K, F x.out := by
  have hF' : ∀ g : G, F (QuotientGroup.mk (s := K) g).out = F g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, hF _ _ k.2]
  let m : G ⧸ K → G ⧸ K := fun x => QuotientGroup.mk (t x.out)
  have hm : Function.Involutive m := fun x => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (t x.out)
    simp only [m]
    rw [hk, map_mul, ht, QuotientGroup.mk_mul_of_mem _ (hK _ k.2), QuotientGroup.out_eq']
  rw [← finsum_comp_equiv (hm.toPerm m) (f := fun x : G ⧸ K => F x.out)]
  exact finsum_congr fun x => (hF' _).symm

section Global

variable (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ}

/- English proof (translation)
Establish `hx : x ≠ 0` using `left_ne_zero_of_mul_eq_one h`. Establish `hy : y ≠ 0` using `right_ne_zero_of_mul_eq_one h`. Establish `h1` using `Formalism.UG.P.spherical_ordV_mul E P x y hx hy`. Establish `h2` using `Formalism.UG.P.spherical_ordV_unit E P 1 1 (one_mem _) (one_mem _) (mul_one 1)`. Rewrite `h1` using `[h, h2]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem ordV_of_mul_eq_one {x y : P.adicCompletion E} (h : x * y = 1) : ordV E P x = -ordV E P y := by
  have hx : x ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hy : y ≠ 0 := right_ne_zero_of_mul_eq_one h
  have h1 := Formalism.UG.P.spherical_ordV_mul E P x y hx hy
  have h2 := Formalism.UG.P.spherical_ordV_unit E P 1 1 (one_mem _) (one_mem _) (mul_one 1)
  rw [h, h2] at h1
  omega

/- English proof (translation)
Unfold `chiDelta`. Rewrite using `[← Equiv.prod_comp (Fin.revPerm : Fin n ≃ Fin n) (fun i : Fin n => (α i.rev)⁻¹ ^ _ * _)]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ordV_of_mul_eq_one E P (theta_diag hb i)]`. Simplify using `only [Fin.revPerm_apply, Fin.rev_rev, inv_zpow']`.

Use `congr 2`. Establish `: ((i.rev : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℂ)`. Rewrite using `[Fin.val_rev, Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chiDelta_theta (α : Fin n → ℂ) {b : GL (Fin n) (P.adicCompletion E)}
    (hb : (b : Matrix (Fin n) (Fin n) (P.adicCompletion E)).BlockTriangular id) :
    chiDelta E P α (theta b) = chiDelta E P (fun i => (α i.rev)⁻¹) b := by
  unfold chiDelta
  rw [← Equiv.prod_comp (Fin.revPerm : Fin n ≃ Fin n) (fun i : Fin n => (α i.rev)⁻¹ ^ _ * _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ordV_of_mul_eq_one E P (theta_diag hb i)]
  simp only [Fin.revPerm_apply, Fin.rev_rev, inv_zpow']
  congr 2
  have : ((i.rev : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℂ) := by
    rw [Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [this]
  push_cast
  ring

end Global

/- English proof (translation)
Introduce `E _ _ P n α φ _ hφ`. Use `⟨fun g => φ (theta g), ?_, by simp, ?_⟩` and prove the remaining obligations. Introduce `b g k hb hk`. Establish `hb'` using `(Formalism.UG.P.spherical_upper_iff b).1 hb`. Simplify using `only [map_mul]`.

Rewrite using `[hφ _ _ _ ((Formalism.UG.P.spherical_upper_iff _).2 (theta_upper hb')) (theta_mem hk), chiDelta_theta E P α hb']`. Introduce `d hd`. Establish `h1 : ((1 : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)).BlockTriangular id` using `Matrix.blockTriangular_one`. Establish `hr : ∀ g, ∀ k ∈ GLint (Fin n) (Ov E P), φ (g * k) = φ g` using `fun g k hk => by`. Use `hφ 1 g k ((Formalism.UG.P.spherical_upper_iff _).2 h1) hk` as an intermediate fact.

Rewrite `this` using `[one_mul, Formalism.UG.P.spherical_chiDelta_int E P α 1 h1 (one_mem _), one_mul]`. Then use the resulting hypothesis. Unfold `hAct`. Simplify using `only [one_mul, divInd_theta _ hd]`. Conclude with `finsum_out_involution _ theta theta_theta (fun k => theta_mem) (fun g => divInd (Ov E P) d g • φ g) (fun g k hk => by rw [divInd_mul_right _ _ _ _ hk, hr g k hk])`.
-/
theorem exists_spherical_dual : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (α : Fin n → ℂ) (φ : GL (Fin n) (P.adicCompletion E) → ℂ), (∀ i, α i ≠ 0) → IsSpherical E P α φ → ∃ φ' : GL (Fin n) (P.adicCompletion E) → ℂ, IsSpherical E P (fun i => (α i.rev)⁻¹) φ' ∧ φ' 1 = φ 1 ∧ ∀ d : List ℤ, d.length = n → hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) (dualLab d)) φ' 1 = hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) d) φ 1 := by
  intro E _ _ P n α φ _ hφ
  refine ⟨fun g => φ (theta g), ?_, by simp, ?_⟩
  · intro b g k hb hk
    have hb' := (Formalism.UG.P.spherical_upper_iff b).1 hb
    simp only [map_mul]
    rw [hφ _ _ _ ((Formalism.UG.P.spherical_upper_iff _).2 (theta_upper hb')) (theta_mem hk), chiDelta_theta E P α hb']
  · intro d hd
    have h1 : ((1 : GL (Fin n) (P.adicCompletion E)) : Matrix (Fin n) (Fin n) (P.adicCompletion E)).BlockTriangular id :=
      Matrix.blockTriangular_one
    have hr : ∀ g, ∀ k ∈ GLint (Fin n) (Ov E P), φ (g * k) = φ g := fun g k hk => by
      have := hφ 1 g k ((Formalism.UG.P.spherical_upper_iff _).2 h1) hk
      rwa [one_mul, Formalism.UG.P.spherical_chiDelta_int E P α 1 h1 (one_mem _), one_mul] at this
    unfold hAct
    simp only [one_mul, divInd_theta _ hd]
    exact finsum_out_involution _ theta theta_theta (fun k => theta_mem)
      (fun g => divInd (Ov E P) d g • φ g) (fun g k hk => by rw [divInd_mul_right _ _ _ _ hk, hr g k hk])

end GlobalTheory.InvTranspose

end
