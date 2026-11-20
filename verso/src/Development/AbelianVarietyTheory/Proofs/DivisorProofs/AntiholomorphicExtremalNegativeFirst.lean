import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorAnnihilatedStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.AntiHol

/- English proof (translation)
Take `⟨hl, r, hr, hS⟩` from `he`. Use `⟨fun a b hab => neg_lt_neg (hl (Fin.rev_lt_rev.2 hab)), fun a => -r (Fin.rev a), fun a => by simp [hr], ?_⟩` and prove the remaining obligations. Rewrite using `[← dualPar_dualPar S, hS]`. Use extensionality with `z`. Simplify using `only [dualPar, Finset.mem_image, Finset.mem_univ, true_and]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨a, rfl⟩, rfl⟩`. Conclude with `⟨Fin.rev a, by simp⟩`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `⟨_, ⟨Fin.rev a, rfl⟩, rfl⟩`.
-/
theorem isEnum_dual {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (dualPar S) lam ε) :
    IsEnum S (fun a => -lam (Fin.rev a)) (fun a => ε (Fin.rev a)) := by
  obtain ⟨hl, r, hr, hS⟩ := he
  refine ⟨fun a b hab => neg_lt_neg (hl (Fin.rev_lt_rev.2 hab)), fun a => -r (Fin.rev a), fun a => by simp [hr], ?_⟩
  rw [← dualPar_dualPar S, hS]
  ext z
  simp only [dualPar, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨Fin.rev a, by simp⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, ⟨Fin.rev a, rfl⟩, rfl⟩

/- English proof (translation)
The claim follows from `Finset.card_equiv Fin.revPerm (by simpa using h)`.
-/
theorem card_rev {n : ℕ} (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q] (h : ∀ b, P b ↔ Q (Fin.rev b)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card :=
  Finset.card_equiv Fin.revPerm (by simpa using h)

/- English proof (translation)
Simplify using `only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Formalism.REAL.rhoN, Formalism.REAL.rhoC]`. Rewrite using `[card_rev (fun b => a < b ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)) (fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)) (fun b => by simp), card_rev (fun b => b < a ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)) (fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)) (fun b => by simp), card_rev (fun b => a < b ∧ ε …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lowK_rev {n : ℕ} (lam : Fin n → ℝ) (ε : Fin n → Bool) (a : Fin n) :
    Formalism.QuantumDeterminants.lowK (fun a => ε (Fin.rev a)) (fun a => -lam (Fin.rev a)) a = -Formalism.QuantumDeterminants.lowK ε lam (Fin.rev a) := by
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Formalism.REAL.rhoN, Formalism.REAL.rhoC]
  rw [card_rev (fun b => a < b ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)) (fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a))
      (fun b => by simp),
    card_rev (fun b => b < a ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)) (fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a))
      (fun b => by simp),
    card_rev (fun b => a < b ∧ ε (Fin.rev b) = ε (Fin.rev a)) (fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a))
      (fun b => by simp),
    card_rev (fun b => b < a ∧ ε (Fin.rev b) = ε (Fin.rev a)) (fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a))
      (fun b => by simp)]
  ring

/- English proof (translation)
Establish `e : negS ε = Finset.univ.map (Fin.castLEEmb hq)`. Use extensionality with `a`. Simplify using `only [negS, Finset.mem_filter, Finset.mem_univ, true_and, h, Finset.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce `ha`.

Establish `ha' : (a : ℕ) < q`. Assume the negation of the conclusion as `hc`. Simplify using `[hc] at ha`. Conclude with `⟨⟨a, ha'⟩, rfl⟩`. Introduce and unpack `⟨i, rfl⟩`.

Simplify using the standard rewrite rules. Establish `hc : (negS ε).card = q` using `by rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]`. Establish `hm : a ∈ negS ε` using `by simpa [negS, h] using ha`. Establish `hf : ∀ i : Fin (negS ε).card, (((negS ε).orderEmbOfFin rfl i : Fin n) : ℕ) = i`. Use `Finset.orderEmbOfFin_unique (s := negS ε) (rfl : (negS ε).card = _) (f := fun i : Fin (negS ε).card => (⟨i, by have := i.2; omega⟩ : Fin n)) (fun i => by have := i.2; simp [negS, h]; omega) (fun i j hij => hij)` as an intermediate fact.

Introduce `i`. Rewrite using `[← this]`. Establish `h1 : revNeg ε a = (revOn ε ⟨a, hm⟩ : Fin n)` using `Equiv.Perm.ofSubtype_apply_of_mem _ hm`. Use `set i := ((negS ε).orderIsoOfFin rfl).symm ⟨a, hm⟩ with hi`. Establish `h2 : (a : ℕ) = i`.

Rewrite using `[← hf i]`. Establish `: ((negS ε).orderIsoOfFin rfl i : Fin n) = a` using `by rw [hi, OrderIso.apply_symm_apply]`. Rewrite using `[← this]`. Both sides reduce to the same expression. Establish `h3 : ((revOn ε ⟨a, hm⟩ : Fin n) : ℕ) = (Fin.rev i : ℕ)` using `hf (Fin.rev i)`.

Rewrite using `[h1, h3, Fin.val_rev]`. Use `i.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem revNeg_first {n q : ℕ} {ε : Fin n → Bool} (hq : q ≤ n) (h : ∀ a, ε a = if (a : ℕ) < q then false else true)
    (a : Fin n) (ha : (a : ℕ) < q) : (revNeg ε a : ℕ) = q - 1 - a := by
  have e : negS ε = Finset.univ.map (Fin.castLEEmb hq) := by
    ext a
    simp only [negS, Finset.mem_filter, Finset.mem_univ, true_and, h, Finset.mem_map]
    constructor
    · intro ha
      have ha' : (a : ℕ) < q := by
        by_contra hc
        simp [hc] at ha
      exact ⟨⟨a, ha'⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      simp
  have hc : (negS ε).card = q := by rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hm : a ∈ negS ε := by simpa [negS, h] using ha
  have hf : ∀ i : Fin (negS ε).card, (((negS ε).orderEmbOfFin rfl i : Fin n) : ℕ) = i := by
    have := Finset.orderEmbOfFin_unique (s := negS ε) (rfl : (negS ε).card = _)
      (f := fun i : Fin (negS ε).card => (⟨i, by have := i.2; omega⟩ : Fin n))
      (fun i => by have := i.2; simp [negS, h]; omega) (fun i j hij => hij)
    intro i
    rw [← this]
  have h1 : revNeg ε a = (revOn ε ⟨a, hm⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ hm
  set i := ((negS ε).orderIsoOfFin rfl).symm ⟨a, hm⟩ with hi
  have h2 : (a : ℕ) = i := by
    rw [← hf i]
    have : ((negS ε).orderIsoOfFin rfl i : Fin n) = a := by rw [hi, OrderIso.apply_symm_apply]
    rw [← this]; rfl
  have h3 : ((revOn ε ⟨a, hm⟩ : Fin n) : ℕ) = (Fin.rev i : ℕ) := hf (Fin.rev i)
  rw [h1, h3, Fin.val_rev]
  have := i.2
  omega

def flipFun {n : ℕ} (q : ℕ) (c : Fin n) : Fin n :=
  if (c : ℕ) < q then c else ⟨n - 1 - (c - q), by have := c.2; omega⟩

/- English proof (translation)
Unfold `flipFun`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem flipFun_val {n : ℕ} (q : ℕ) (c : Fin n) :
    (flipFun q c : ℕ) = if (c : ℕ) < q then (c : ℕ) else n - 1 - (c - q) := by
  unfold flipFun
  split_ifs <;> rfl

/- English proof (translation)
Introduce `c` and use `by apply Fin.ext have := c.2 rw [flipFun_val, flipFun_val] split_ifs <;> omega`.
-/
theorem flipFun_invol {n : ℕ} (q : ℕ) : Function.Involutive (flipFun (n := n) q) := fun c => by
  apply Fin.ext
  have := c.2
  rw [flipFun_val, flipFun_val]
  split_ifs <;> omega

def flipPerm {n : ℕ} (q : ℕ) : Equiv.Perm (Fin n) := (flipFun_invol q).toPerm

/- English proof (translation)
The claim follows from `flipFun_val q c`.
-/
theorem flipPerm_val {n : ℕ} (q : ℕ) (c : Fin n) :
    (flipPerm q c : ℕ) = if (c : ℕ) < q then (c : ℕ) else n - 1 - (c - q) := flipFun_val q c

/- English proof (translation)
Establish `hok` using `Formalism.L2.NTheta.holOK_kapW h p q hpq`. Take `⟨rfl, h1⟩` from `GlobalTheory.HolDS.enum_holPar hok (isEnum_dual he)`. Take `⟨_, h2⟩` from `GlobalTheory.HolDS.lowK_holPar hok (isEnum_dual he)`. Simplify using `only [Fin.cast_eq_self, lowK_rev] at h1 h2`. Establish `hε : ∀ a, ε a = if (a : ℕ) < q then false else true`.

Introduce `a`. Take `⟨x, hx⟩` from `finSumFinEquiv.surjective (Fin.rev a)`. Establish `h3` using `(h1 x).2`. Rewrite `h3` using `[hx, Fin.rev_rev]`. Establish `h4` using `congrArg Fin.val hx`.

Use `a.2` as an intermediate fact. Break down `x with i | i` into its components or cases. Use `i.2` as an intermediate fact. Simplify using `at h4`. Rewrite using `[h3, if_neg (by omega)]; rfl`.

Use `i.2` as an intermediate fact. Simplify using `at h4`. Rewrite using `[h3, if_pos (by omega)]; rfl`. Use `⟨hε, fun c => ?_⟩` and prove the remaining obligations. Establish `hc` using `c.2`.

Establish `hv` using `flipPerm_val q c`. Distinguish the cases in `hcq : (c : ℕ) < q`. Rewrite `hv` using `[if_pos hcq]`. Establish `h5` using `revNeg_first (by omega) hε (flipPerm q c) (by omega)`. Establish `h6 : revNeg ε (flipPerm q c) = Fin.rev (finSumFinEquiv (Sum.inr ⟨c, hcq⟩))`.

Apply `Fin.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite using `[h6, ← neg_eq_iff_eq_neg, h2]`. Simplify using `[wtCol, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, hcq]`.

Rewrite `hv` using `[if_neg hcq]`. Establish `h5` using `revNeg_of_pos ε (a := flipPerm q c) (by rw [hε, if_neg (by omega)])`. Establish `h6 : revNeg ε (flipPerm q c) = Fin.rev (finSumFinEquiv (Sum.inl ⟨c - q, by omega⟩))`. Rewrite using `[h5]`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite using `[h6, ← neg_eq_iff_eq_neg, h2]`. Simplify using `[wtCol, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, hcq]`.
-/
theorem shape {R : Ranks} (h : HCParam R) {p q n : ℕ} (hpq : p + q = R.r) {lam : Fin n → ℝ} {ε : Fin n → Bool}
    (he : IsEnum (dualPar (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q))) lam ε) :
    (∀ a, ε a = if (a : ℕ) < q then false else true) ∧
      ∀ c, Formalism.QuantumDeterminants.lowK ε lam (revNeg ε (flipPerm q c)) = -(wtCol h p q c : ℝ) := by
  have hok := Formalism.L2.NTheta.holOK_kapW h p q hpq
  obtain ⟨rfl, h1⟩ := GlobalTheory.HolDS.enum_holPar hok (isEnum_dual he)
  obtain ⟨_, h2⟩ := GlobalTheory.HolDS.lowK_holPar hok (isEnum_dual he)
  simp only [Fin.cast_eq_self, lowK_rev] at h1 h2
  have hε : ∀ a, ε a = if (a : ℕ) < q then false else true := by
    intro a
    obtain ⟨x, hx⟩ := finSumFinEquiv.surjective (Fin.rev a)
    have h3 := (h1 x).2
    rw [hx, Fin.rev_rev] at h3
    have h4 := congrArg Fin.val hx
    have := a.2
    rcases x with i | i
    · have := i.2
      simp at h4
      rw [h3, if_neg (by omega)]; rfl
    · have := i.2
      simp at h4
      rw [h3, if_pos (by omega)]; rfl
  refine ⟨hε, fun c => ?_⟩
  have hc := c.2
  have hv := flipPerm_val q c
  by_cases hcq : (c : ℕ) < q
  · rw [if_pos hcq] at hv
    have h5 := revNeg_first (by omega) hε (flipPerm q c) (by omega)
    have h6 : revNeg ε (flipPerm q c) = Fin.rev (finSumFinEquiv (Sum.inr ⟨c, hcq⟩)) := by
      apply Fin.ext
      simp
      omega
    rw [h6, ← neg_eq_iff_eq_neg, h2]
    simp [wtCol, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, hcq]
  · rw [if_neg hcq] at hv
    have h5 := revNeg_of_pos ε (a := flipPerm q c) (by rw [hε, if_neg (by omega)])
    have h6 : revNeg ε (flipPerm q c) = Fin.rev (finSumFinEquiv (Sum.inl ⟨c - q, by omega⟩)) := by
      rw [h5]
      apply Fin.ext
      simp
      omega
    rw [h6, ← neg_eq_iff_eq_neg, h2]
    simp [wtCol, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, hcq]

variable {D : D7} (θ : InfFam D) (V : HSp D)

/- English proof (translation)
Use function extensionality and compare the values at `g`. Use `deriv_comp_neg (fun t : ℝ => φ (g * oneP θ V ρ X t)) 0` as an intermediate fact. Simplify `this` using `only [Rder, oneP, smul_neg, neg_smul, neg_zero, Pi.neg_apply]`.
-/
theorem Rder_neg (ρ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V ρ (-X) φ = -Rder θ V ρ X φ := by
  funext g
  have := deriv_comp_neg (fun t : ℝ => φ (g * oneP θ V ρ X t)) 0
  simpa only [Rder, oneP, smul_neg, neg_smul, neg_zero, Pi.neg_apply] using this

/- English proof (translation)
The claim follows from `deriv.star`.
-/
theorem Rder_conj (ρ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) (g : GA D V) :
    Rder θ V ρ X (fun g => starRingEnd ℂ (φ g)) g = starRingEnd ℂ (Rder θ V ρ X φ g) :=
  deriv.star

/- English proof (translation)
Establish `h : conjAt V ρ (-Z) = -conjAt V ρ Z` using `by simp [conjAt]`. Unfold `RderC`. Rewrite using `[h, ← neg_add, neg_sub_neg, ← neg_sub Z, smul_neg, smul_neg, Rder_neg, Rder_neg, smul_neg, neg_add]`.
-/
theorem RderC_neg (ρ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V ρ (-Z) φ = -RderC θ V ρ Z φ := by
  have h : conjAt V ρ (-Z) = -conjAt V ρ Z := by simp [conjAt]
  unfold RderC
  rw [h, ← neg_add, neg_sub_neg, ← neg_sub Z, smul_neg, smul_neg, Rder_neg, Rder_neg, smul_neg, neg_add]

/- English proof (translation)
Unfold `RderC`. Rewrite using `[hZ, add_comm (conjAt V ρ Z), ← neg_sub Z, smul_neg, Rder_neg]`. Simplify using `[Rder_conj]`.
-/
theorem RderC_conj (ρ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hZ : conjAt V ρ (conjAt V ρ Z) = Z)
    (φ : GA D V → ℂ) (g : GA D V) :
    RderC θ V ρ Z (fun g => starRingEnd ℂ (φ g)) g = starRingEnd ℂ (RderC θ V ρ (conjAt V ρ Z) φ g) := by
  unfold RderC
  rw [hZ, add_comm (conjAt V ρ Z), ← neg_sub Z, smul_neg, Rder_neg]
  simp [Rder_conj]

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

/- English proof (translation)
Unfold `Formalism.REAL.Jm`. Rewrite using `[diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[Pi.star_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Jm_herm {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  rw [Pi.star_apply]
  split_ifs <;> simp

variable {V} {S : D.what₂.Tau → SPar} (M : DSModel V S)

/- English proof (translation)
Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)`. Establish `h1 : M.fr ρ * (M.fr ρ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hd`. Establish `h3 : (M.fr ρ)⁻¹ᴴ * (M.fr ρ)ᴴ = 1` using `by rw [← conjTranspose_mul, h1, conjTranspose_one]`. Establish `h4 : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, (M.fr ρ)⁻¹ᴴ * ((M.fr ρ)ᴴ * Y) = Y` using `fun Y => by`. Rewrite using `[← Matrix.mul_assoc, h3, Matrix.one_mul]`.

Unfold `conjAt`. Rewrite using `[← M.fr_gram ρ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (Jm_mul_self (M.ε ρ)), ← conjTranspose_nonsing_inv]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc, h4, Matrix.mul_neg, Matrix.neg_mul]`.
-/
theorem conjAt_frame (ρ : D.what₂.Tau) (W : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    conjAt V ρ ((M.fr ρ)⁻¹ * W * M.fr ρ) =
      (M.fr ρ)⁻¹ * (-(Formalism.REAL.Jm (M.ε ρ) * Wᴴ * Formalism.REAL.Jm (M.ε ρ))) * M.fr ρ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
  have h1 : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h3 : (M.fr ρ)⁻¹ᴴ * (M.fr ρ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h4 : ∀ Y : Matrix (Fin V.rank) (Fin V.rank) ℂ, (M.fr ρ)⁻¹ᴴ * ((M.fr ρ)ᴴ * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  unfold conjAt
  rw [← M.fr_gram ρ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (Jm_mul_self (M.ε ρ)),
    ← conjTranspose_nonsing_inv]
  simp only [conjTranspose_mul, Matrix.mul_assoc, h4, Matrix.mul_neg, Matrix.neg_mul]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Rewrite using `[RderC_conj, conjAt_frame]`. Establish `h1 : Formalism.REAL.Jm (M.ε ρ) * (Matrix.single a b (1 : ℂ))ᴴ * Formalism.REAL.Jm (M.ε ρ) = Matrix.single b a 1 ∨ Formalism.REAL.Jm (M.ε ρ) * (Matrix.single a b (1 : ℂ))ᴴ * Formalism.REAL.Jm (M.ε ρ) = -Matrix.single b a 1`. Unfold `Formalism.REAL.Jm`. Distinguish the cases in `hab : M.ε ρ a = M.ε ρ b`.

Use `left`. Use extensionality with `i j`. Simplify using `only [mul_diagonal, diagonal_mul, conjTranspose_apply, Matrix.single_apply]`. Distinguish the cases in `hij : a = j ∧ b = i`. Take `⟨rfl, rfl⟩` from `hij`.

Rewrite using `[hab]`. Apply the tactic sequence `split_ifs <;> simp_all`. Rewrite using `[if_neg hij, if_neg (fun h' : b = i ∧ a = j => hij h'.symm)]`. Simplify using the standard rewrite rules. Use `right`.

Use extensionality with `i j`. Simplify using `only [mul_diagonal, diagonal_mul, conjTranspose_apply, Matrix.single_apply, Matrix.neg_apply]`. Distinguish the cases in `hij : a = j ∧ b = i`. Apply the tactic sequence `obtain ⟨rfl, rfl⟩ := hij split_ifs <;> simp_all`. Rewrite using `[if_neg hij, if_neg (fun h' : b = i ∧ a = j => hij h'.symm)]`.

Simplify using the standard rewrite rules. Break down `h1 with h1 | h1` into its components or cases. Rewrite using `[h1, Matrix.mul_neg, Matrix.neg_mul, RderC_neg, h]`. Simplify using the standard rewrite rules. Rewrite using `[h1, neg_neg, h]`.

Simplify using the standard rewrite rules. Rewrite using `[conjAt_frame, conjAt_frame]`. Use `congr 2`. Simplify using `only [conjTranspose_neg, conjTranspose_mul, Jm_herm, conjTranspose_conjTranspose, Matrix.mul_neg, Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]`.
-/
theorem conj_killed (ρ : D.what₂.Tau) (a b : Fin V.rank) (φ : GA D V → ℂ)
    (h : RderC θ V ρ ((M.fr ρ)⁻¹ * Matrix.single b a 1 * M.fr ρ) φ = 0) :
    RderC θ V ρ ((M.fr ρ)⁻¹ * Matrix.single a b 1 * M.fr ρ) (fun g => starRingEnd ℂ (φ g)) = 0 := by
  funext g
  rw [RderC_conj, conjAt_frame]
  · have h1 : Formalism.REAL.Jm (M.ε ρ) * (Matrix.single a b (1 : ℂ))ᴴ * Formalism.REAL.Jm (M.ε ρ) = Matrix.single b a 1 ∨
        Formalism.REAL.Jm (M.ε ρ) * (Matrix.single a b (1 : ℂ))ᴴ * Formalism.REAL.Jm (M.ε ρ) = -Matrix.single b a 1 := by
      unfold Formalism.REAL.Jm
      by_cases hab : M.ε ρ a = M.ε ρ b
      · left
        ext i j
        simp only [mul_diagonal, diagonal_mul, conjTranspose_apply, Matrix.single_apply]
        by_cases hij : a = j ∧ b = i
        · obtain ⟨rfl, rfl⟩ := hij
          rw [hab]
          split_ifs <;> simp_all
        · rw [if_neg hij, if_neg (fun h' : b = i ∧ a = j => hij h'.symm)]
          simp
      · right
        ext i j
        simp only [mul_diagonal, diagonal_mul, conjTranspose_apply, Matrix.single_apply, Matrix.neg_apply]
        by_cases hij : a = j ∧ b = i
        · obtain ⟨rfl, rfl⟩ := hij
          split_ifs <;> simp_all
        · rw [if_neg hij, if_neg (fun h' : b = i ∧ a = j => hij h'.symm)]
          simp
    rcases h1 with h1 | h1
    · rw [h1, Matrix.mul_neg, Matrix.neg_mul, RderC_neg, h]
      simp
    · rw [h1, neg_neg, h]
      simp
  · rw [conjAt_frame, conjAt_frame]
    congr 2
    simp only [conjTranspose_neg, conjTranspose_mul, Jm_herm, conjTranspose_conjTranspose, Matrix.mul_neg,
      Matrix.neg_mul, neg_neg, ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
    rw [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]

/- English proof (translation)
Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 hA`. Establish `h1 : (A⁻¹.submatrix id e)⁻¹ = A.submatrix e id`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hd, submatrix_id_id]`. Rewrite using `[h1, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]`.
-/
theorem perm_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) (e : Equiv.Perm (Fin n))
    (W : Matrix (Fin n) (Fin n) ℂ) :
    A⁻¹.submatrix id e * W.submatrix e e * (A⁻¹.submatrix id e)⁻¹ = A⁻¹ * W * A := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hA
  have h1 : (A⁻¹.submatrix id e)⁻¹ = A.submatrix e id := by
    apply Matrix.inv_eq_right_inv
    rw [submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hd, submatrix_id_id]
  rw [h1, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id]

end GlobalTheory.HolRead.AntiHol

open GlobalTheory.HolRead.AntiHol in

/- English proof (translation)
Introduce `D θ V S M h p q hθ hpq hV hS v hv`. Establish `hsh` using `fun ρ => shape (h ρ) hpq (hS ρ ▸ M.enum ρ)`. Use `⟨fun ρ => (M.fr ρ)⁻¹.submatrix id (flipPerm q), fun ρ => ?_, fun J χ T hT => ⟨?_, fun ρ c d hcd => ?_, fun ρ t g => ?_⟩⟩` and prove the remaining obligations. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)`. Establish `h1 : M.fr ρ * (M.fr ρ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hd`.

Establish `h2 : (M.fr ρ)⁻¹ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹ = Formalism.REAL.Jm (M.ε ρ)`. Rewrite using `[← M.fr_gram ρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]`. Establish `h3 : ((M.fr ρ)⁻¹.submatrix id (flipPerm q))ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹.submatrix id (flipPerm q) = ((M.fr ρ)⁻¹ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹).submatrix (flipPerm q) (flipPerm q)` using `rfl`. Use `beta_reduce`. Rewrite using `[h3, h2, Formalism.REAL.Jm, submatrix_diagonal_equiv]`.

Use `congr 1`. Use function extensionality and compare the values at `c`. Use `c.2` as an intermediate fact. Establish `hv` using `flipPerm_val q c`. Simplify using `only [Function.comp, (hsh ρ).1]`.

Distinguish the cases in `hc : (c : ℕ) < q`. Rewrite `hv` using `[if_pos hc]`. Simplify using `[hv, hc]`. Rewrite `hv` using `[if_neg hc]`. Establish `: ¬ (flipPerm q c : ℕ) < q` using `by omega`.

Simplify using `[this, hc]`. Introduce `k τs Xs hX g`. Conclude with `Complex.conjCLE.contDiff.comp ((hT.aut v).smooth k τs Xs hX g)`. Establish `hk` using `(GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ q false (hsh ρ).1).1 (flipPerm q d) (flipPerm q c) (by`. Use `c.2` as an intermediate fact.

Use `d.2` as an intermediate fact. Establish `hc` using `flipPerm_val q c`. Establish `hd` using `flipPerm_val q d`. Establish `hcd' : (c : ℕ) < d` using `hcd`. Simplify using `only [KillPair, (hsh ρ).1, Fin.lt_def]`.

Apply the tactic sequence `split_ifs at hc hd <;> split_ifs <;> simp <;> omega)`. Establish `h1 : Matrix.single c d (1 : ℂ) = (Matrix.single (flipPerm q c) (flipPerm q d) 1).submatrix (flipPerm q) (flipPerm q)`. Use extensionality with `i j`. Simplify using `[Matrix.single_apply]`. Use `beta_reduce`.

Rewrite using `[h1, perm_conj _ (M.fr_unit ρ)]`. Conclude with `conj_killed θ M ρ _ _ _ hk`. Establish `hk` using `(GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ q false (hsh ρ).1).2 (fun a => t ((flipPerm q).symm a)) g`. Establish `h1 : diagonal (fun c => Complex.exp ((t c : ℂ) * Complex.I)) = (diagonal fun a => Complex.exp ((t ((flipPerm q).symm a) : ℂ) * Complex.I)).submatrix (flipPerm q) (flipPerm q)`. Rewrite using `[submatrix_diagonal_equiv]`.

Use `congr 1`. Use function extensionality and compare the values at `c`. Simplify using the standard rewrite rules. Use `beta_reduce`. Rewrite using `[h1, perm_conj _ (M.fr_unit ρ), hk, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Equiv.sum_comp (flipPerm q)]`.

Use `congr 2`. Simplify using `only [extWt, (hsh ρ).2, Equiv.symm_apply_apply, neg_mul, Finset.sum_neg_distrib]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.HolRead.conj_extVec_isHolFor : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (h : D.what₂.Tau → HCParam D.R) (p q : ℕ), IsInfFam θ → p + q = D.R.r → V.rank = D.R.r → (∀ ρ, S ρ = dualPar (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW (h ρ) p q))) → ∀ v : M.Vec, IsExtVec M v → ∃ x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, NegFirst V q x ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsMultMap θ M J χ T → IsHolFor θ V x (fun ρ c => wtCol (h ρ) p q c) (fun g => starRingEnd ℂ (T v g)) := by
  intro D θ V S M h p q hθ hpq hV hS v hv
  have hsh := fun ρ => shape (h ρ) hpq (hS ρ ▸ M.enum ρ)
  refine ⟨fun ρ => (M.fr ρ)⁻¹.submatrix id (flipPerm q), fun ρ => ?_, fun J χ T hT => ⟨?_, fun ρ c d hcd => ?_, fun ρ t g => ?_⟩⟩
  · have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit ρ)
    have h1 : M.fr ρ * (M.fr ρ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
    have h2 : (M.fr ρ)⁻¹ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹ = Formalism.REAL.Jm (M.ε ρ) := by
      rw [← M.fr_gram ρ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, h1, conjTranspose_one,
        Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have h3 : ((M.fr ρ)⁻¹.submatrix id (flipPerm q))ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹.submatrix id (flipPerm q) =
        ((M.fr ρ)⁻¹ᴴ * gramAt D V ρ * (M.fr ρ)⁻¹).submatrix (flipPerm q) (flipPerm q) := rfl
    beta_reduce
    rw [h3, h2, Formalism.REAL.Jm, submatrix_diagonal_equiv]
    congr 1
    funext c
    have := c.2
    have hv := flipPerm_val q c
    simp only [Function.comp, (hsh ρ).1]
    by_cases hc : (c : ℕ) < q
    · rw [if_pos hc] at hv
      simp [hv, hc]
    · rw [if_neg hc] at hv
      have : ¬ (flipPerm q c : ℕ) < q := by omega
      simp [this, hc]
  · intro k τs Xs hX g
    exact Complex.conjCLE.contDiff.comp ((hT.aut v).smooth k τs Xs hX g)
  · have hk := (GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ q false (hsh ρ).1).1 (flipPerm q d) (flipPerm q c) (by
      have := c.2
      have := d.2
      have hc := flipPerm_val q c
      have hd := flipPerm_val q d
      have hcd' : (c : ℕ) < d := hcd
      simp only [KillPair, (hsh ρ).1, Fin.lt_def]
      split_ifs at hc hd <;> split_ifs <;> simp <;> omega)
    have h1 : Matrix.single c d (1 : ℂ) =
        (Matrix.single (flipPerm q c) (flipPerm q d) 1).submatrix (flipPerm q) (flipPerm q) := by
      ext i j
      simp [Matrix.single_apply]
    beta_reduce
    rw [h1, perm_conj _ (M.fr_unit ρ)]
    exact conj_killed θ M ρ _ _ _ hk
  · have hk := (GlobalTheory.T.extremal_vector_annihilated D θ V S M J χ T hθ hT v hv ρ q false (hsh ρ).1).2 (fun a => t ((flipPerm q).symm a)) g
    have h1 : diagonal (fun c => Complex.exp ((t c : ℂ) * Complex.I)) =
        (diagonal fun a => Complex.exp ((t ((flipPerm q).symm a) : ℂ) * Complex.I)).submatrix (flipPerm q) (flipPerm q) := by
      rw [submatrix_diagonal_equiv]
      congr 1
      funext c
      simp
    beta_reduce
    rw [h1, perm_conj _ (M.fr_unit ρ), hk, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      ← Equiv.sum_comp (flipPerm q)]
    congr 2
    simp only [extWt, (hsh ρ).2, Equiv.symm_apply_apply, neg_mul, Finset.sum_neg_distrib]
    push_cast
    ring

end
