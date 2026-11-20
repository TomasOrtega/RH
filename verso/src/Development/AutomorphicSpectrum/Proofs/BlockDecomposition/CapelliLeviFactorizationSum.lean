import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.CTFin.CapFactor

/- English proof (translation)
The claim follows from `Fin.sum_univ_two n`.
-/
theorem two_sum (n : Fin 2 → ℕ) : ∑ i, n i = n 0 + n 1 := Fin.sum_univ_two n

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Use `(stdBlocks_val n h 0 i).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem std_zero (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1) (i : Fin (n 0)) :
    stdBlocks n h ⟨0, i⟩ = Fin.castAdd (n 1) i := by
  apply Fin.ext
  refine (stdBlocks_val n h 0 i).trans ?_
  simp

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Use `(stdBlocks_val n h 1 i).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem std_one (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1) (i : Fin (n 1)) :
    stdBlocks n h ⟨1, i⟩ = Fin.natAdd (n 0) i := by
  apply Fin.ext
  refine (stdBlocks_val n h 1 i).trans ?_
  simp

/- English proof (translation)
Establish `h1 : (Finset.univ.filter fun b : Fin 2 => (0 : Fin 2) < b) = {1}` using `by decide`. Simplify using `[modExp, h1]`.
-/
theorem modExp_zero (n : Fin 2 → ℕ) : modExp (fun i => Fin (n i)) 0 = n 1 := by
  have h1 : (Finset.univ.filter fun b : Fin 2 => (0 : Fin 2) < b) = {1} := by decide
  simp [modExp, h1]

/- English proof (translation)
Establish `h1 : (Finset.univ.filter fun b : Fin 2 => (1 : Fin 2) < b) = ∅` using `by decide`. Simplify using `[modExp, h1, Finset.sum_filter]`.
-/
theorem modExp_one (n : Fin 2 → ℕ) : modExp (fun i => Fin (n i)) 1 = -(n 0 : ℤ) := by
  have h1 : (Finset.univ.filter fun b : Fin 2 => (1 : Fin 2) < b) = ∅ := by decide
  simp [modExp, h1, Finset.sum_filter]

/- English proof (translation)
Take `⟨hp, hd⟩` from `mem_unipRad.1 hv`. Establish `hp'` using `mem_parab_iff.1 hp`. Establish `A : ∀ i j : Fin (n 0), (v : Matrix _ _ R) (Fin.castAdd (n 1) i) (Fin.castAdd (n 1) j) = (1 : Matrix (Fin (n 0)) (Fin (n 0)) R) i j`. Introduce `i j`. Use `hd 0 i j` as an intermediate fact.

Rewrite `this` using `[std_zero, std_zero]`. Then use the resulting hypothesis. Establish `B : ∀ i j : Fin (n 1), (v : Matrix _ _ R) (Fin.natAdd (n 0) i) (Fin.natAdd (n 0) j) = (1 : Matrix (Fin (n 1)) (Fin (n 1)) R) i j`. Introduce `i j`. Use `hd 1 i j` as an intermediate fact. Rewrite `this` using `[std_one, std_one]`. Then use the resulting hypothesis.

Establish `C : ∀ (i : Fin (n 1)) (j : Fin (n 0)), (v : Matrix _ _ R) (Fin.natAdd (n 0) i) (Fin.castAdd (n 1) j) = 0`. Introduce `i j`. Use `hp' 1 0 i j (by decide)` as an intermediate fact. Rewrite `this` using `[std_one, std_zero]`. Then use the resulting hypothesis. Use `⟨fun p => (v : Matrix (Fin (n 0 + n 1)) (Fin (n 0 + n 1)) R) p.1.1 p.1.2, Units.ext ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(v : Matrix (Fin (n 0 + n 1)) (Fin (n 0 + n 1)) R) = 1 + nilM _`. Use extensionality with `i j`. Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j`. Establish `: ¬ (((Fin.castAdd (n 1) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.castAdd (n 1) j : Fin (n 0 + n 1)) : ℕ))`. Simplify using `only [Fin.val_castAdd]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, add_zero, A, Matrix.one_apply, Fin.castAdd_inj]`. Establish `: (((Fin.castAdd (n 1) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.natAdd (n 0) j : Fin (n 0 + n 1)) : ℕ))`. Simplify using `only [Fin.val_castAdd, Fin.val_natAdd]`. Use linear arithmetic over natural numbers and integers.

Establish `hne : (Fin.castAdd (n 1) i : Fin (n 0 + n 1)) ≠ Fin.natAdd (n 0) j`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [Fin.val_castAdd, Fin.val_natAdd] at this`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [Matrix.add_apply, nilM, Matrix.of_apply, dif_pos this, Matrix.one_apply, if_neg hne, zero_add]`. Establish `: ¬ (((Fin.natAdd (n 0) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.castAdd (n 1) j : Fin (n 0 + n 1)) : ℕ))`. Simplify using `only [Fin.val_castAdd, Fin.val_natAdd]`. Use linear arithmetic over natural numbers and integers. Establish `hne : (Fin.natAdd (n 0) i : Fin (n 0 + n 1)) ≠ Fin.castAdd (n 1) j`.

Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [Fin.val_castAdd, Fin.val_natAdd] at this`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, Matrix.one_apply, if_neg hne, add_zero, C]`.

Establish `: ¬ (((Fin.natAdd (n 0) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.natAdd (n 0) j : Fin (n 0 + n 1)) : ℕ))`. Simplify using `only [Fin.val_natAdd]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, add_zero, B, Matrix.one_apply, Fin.natAdd_inj]`.
-/
theorem exists_unip_of_mem {R : Type} [CommRing R] (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1)
    {v : GL (Fin (n 0 + n 1)) R} (hv : v ∈ unipRad R (stdBlocks n h)) :
    ∃ x : BlockIx (n 0 + n 1) (n 0) → R, v = unip x := by
  obtain ⟨hp, hd⟩ := mem_unipRad.1 hv
  have hp' := mem_parab_iff.1 hp
  have A : ∀ i j : Fin (n 0), (v : Matrix _ _ R) (Fin.castAdd (n 1) i) (Fin.castAdd (n 1) j) =
      (1 : Matrix (Fin (n 0)) (Fin (n 0)) R) i j := by
    intro i j
    have := hd 0 i j
    rwa [std_zero, std_zero] at this
  have B : ∀ i j : Fin (n 1), (v : Matrix _ _ R) (Fin.natAdd (n 0) i) (Fin.natAdd (n 0) j) =
      (1 : Matrix (Fin (n 1)) (Fin (n 1)) R) i j := by
    intro i j
    have := hd 1 i j
    rwa [std_one, std_one] at this
  have C : ∀ (i : Fin (n 1)) (j : Fin (n 0)), (v : Matrix _ _ R) (Fin.natAdd (n 0) i) (Fin.castAdd (n 1) j) = 0 := by
    intro i j
    have := hp' 1 0 i j (by decide)
    rwa [std_one, std_zero] at this
  refine ⟨fun p => (v : Matrix (Fin (n 0 + n 1)) (Fin (n 0 + n 1)) R) p.1.1 p.1.2, Units.ext ?_⟩
  change (v : Matrix (Fin (n 0 + n 1)) (Fin (n 0 + n 1)) R) = 1 + nilM _
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have : ¬ (((Fin.castAdd (n 1) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.castAdd (n 1) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_castAdd]; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, add_zero, A, Matrix.one_apply, Fin.castAdd_inj]
  · have : (((Fin.castAdd (n 1) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.natAdd (n 0) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
    have hne : (Fin.castAdd (n 1) i : Fin (n 0 + n 1)) ≠ Fin.natAdd (n 0) j := by
      intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_pos this, Matrix.one_apply, if_neg hne, zero_add]
  · have : ¬ (((Fin.natAdd (n 0) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.castAdd (n 1) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
    have hne : (Fin.natAdd (n 0) i : Fin (n 0 + n 1)) ≠ Fin.castAdd (n 1) j := by
      intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, Matrix.one_apply, if_neg hne, add_zero, C]
  · have : ¬ (((Fin.natAdd (n 0) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.natAdd (n 0) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_natAdd]; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, add_zero, B, Matrix.one_apply, Fin.natAdd_inj]

def levPair {R : Type} [CommRing R] {n : Fin 2 → ℕ} (g : GL (Fin (n 0)) R × GL (Fin (n 1)) R) :
    ∀ i : Fin 2, GL (Fin (n i)) R
  | ⟨0, _⟩ => g.1
  | ⟨1, _⟩ => g.2

/- English proof (translation)
Establish `p0 : ∀ i : Fin (n 0), two (stdSum (rfl : n 0 + n 1 = n 0 + n 1)) ⟨false, i⟩ = stdBlocks n h ⟨0, i⟩` using `fun i => by`. Rewrite using `[std_zero, two_false]; exact Fin.ext (by simp)`. Establish `p1 : ∀ i : Fin (n 1), two (stdSum (rfl : n 0 + n 1 = n 0 + n 1)) ⟨true, i⟩ = stdBlocks n h ⟨1, i⟩` using `fun i => by`. Rewrite using `[std_one, two_true]; exact Fin.ext (by simp)`. Establish `key : ∀ (a b : Fin 2) (i : Fin (n a)) (j : Fin (n b)), (lev R (n 0) (n 1) g : Matrix _ _ R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) = (leviEmb R (stdBlocks n h) (levPair g) : Matrix _ _ R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩)`.

Use `Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun i j => ?_, fun i j => ?_⟩, Fin.forall_fin_two.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[leviEmb_apply_same, ← p0, ← p0]`. Conclude with `leviEmb_apply_same R (two _) (leviTwo R _ _ g) false i j`. Rewrite using `[leviEmb_apply_ne R _ _ (a := 0) (b := 1) (by decide), ← p0, ← p1]`. Conclude with `leviEmb_apply_ne R (two _) (leviTwo R _ _ g) (a := false) (b := true) (by simp) i j`.

Rewrite using `[leviEmb_apply_ne R _ _ (a := 1) (b := 0) (by decide), ← p0, ← p1]`. Conclude with `leviEmb_apply_ne R (two _) (leviTwo R _ _ g) (a := true) (b := false) (by simp) i j`. Rewrite using `[leviEmb_apply_same, ← p1, ← p1]`. Conclude with `leviEmb_apply_same R (two _) (leviTwo R _ _ g) true i j`. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Take `⟨⟨a, i⟩, rfl⟩` from `(stdBlocks n h).surjective i`. Take `⟨⟨b, j⟩, rfl⟩` from `(stdBlocks n h).surjective j`. Conclude with `key a b i j`.
-/
theorem lev_eq_leviEmb {R : Type} [CommRing R] (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1)
    (g : GL (Fin (n 0)) R × GL (Fin (n 1)) R) :
    lev R (n 0) (n 1) g = leviEmb R (stdBlocks n h) (levPair g) := by
  have p0 : ∀ i : Fin (n 0), two (stdSum (rfl : n 0 + n 1 = n 0 + n 1)) ⟨false, i⟩ = stdBlocks n h ⟨0, i⟩ := fun i => by
    rw [std_zero, two_false]; exact Fin.ext (by simp)
  have p1 : ∀ i : Fin (n 1), two (stdSum (rfl : n 0 + n 1 = n 0 + n 1)) ⟨true, i⟩ = stdBlocks n h ⟨1, i⟩ := fun i => by
    rw [std_one, two_true]; exact Fin.ext (by simp)
  have key : ∀ (a b : Fin 2) (i : Fin (n a)) (j : Fin (n b)),
      (lev R (n 0) (n 1) g : Matrix _ _ R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) =
      (leviEmb R (stdBlocks n h) (levPair g) : Matrix _ _ R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) := by
    refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun i j => ?_, fun i j => ?_⟩,
      Fin.forall_fin_two.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
    · rw [leviEmb_apply_same, ← p0, ← p0]
      exact leviEmb_apply_same R (two _) (leviTwo R _ _ g) false i j
    · rw [leviEmb_apply_ne R _ _ (a := 0) (b := 1) (by decide), ← p0, ← p1]
      exact leviEmb_apply_ne R (two _) (leviTwo R _ _ g) (a := false) (b := true) (by simp) i j
    · rw [leviEmb_apply_ne R _ _ (a := 1) (b := 0) (by decide), ← p0, ← p1]
      exact leviEmb_apply_ne R (two _) (leviTwo R _ _ g) (a := true) (b := false) (by simp) i j
    · rw [leviEmb_apply_same, ← p1, ← p1]
      exact leviEmb_apply_same R (two _) (leviTwo R _ _ g) true i j
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks n h).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks n h).surjective j
  exact key a b i j

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Use `map_qdet S.val (fun i j => (⟨X i j, hX i j⟩ : S)) u` as an intermediate fact. Simplify using `only [Subalgebra.coe_val] at this`. Rewrite using `[← this]`. Conclude with `(Formalism.REAL.qdet _ _ : S).2`.
-/
theorem qdet_mem {A : Type} [Ring A] [Algebra ℂ A] {a : ℕ} (S : Subalgebra ℂ A) (X : Fin a → Fin a → A)
    (hX : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  have := map_qdet S.val (fun i j => (⟨X i j, hX i j⟩ : S)) u
  simp only [Subalgebra.coe_val] at this
  rw [← this]
  exact (Formalism.REAL.qdet _ _ : S).2

/- English proof (translation)
Establish `h` using `glRel_Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j) (Fin.natAdd r k) (Fin.natAdd r l)`. Establish `h1 : (Fin.castAdd s j : Fin (r + s)) ≠ Fin.natAdd r k`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [Fin.val_castAdd, Fin.val_natAdd] at this`.

Use linear arithmetic over natural numbers and integers. Establish `h2 : (Fin.natAdd r l : Fin (r + s)) ≠ Fin.castAdd s i`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [Fin.val_castAdd, Fin.val_natAdd] at this`.

Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[if_neg h1, if_neg h2, sub_zero]`. Conclude with `sub_eq_zero.1 h`.
-/
theorem Eop_commute_blocks (r s : ℕ) (τ : E →+* ℂ) (i j : Fin r) (k l : Fin s) :
    Commute (Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j))
      (Eop (a := r + s) τ (Fin.natAdd r k) (Fin.natAdd r l)) := by
  have h := glRel_Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j) (Fin.natAdd r k) (Fin.natAdd r l)
  have h1 : (Fin.castAdd s j : Fin (r + s)) ≠ Fin.natAdd r k := by
    intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  have h2 : (Fin.natAdd r l : Fin (r + s)) ≠ Fin.castAdd s i := by
    intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  rw [if_neg h1, if_neg h2, sub_zero] at h
  exact sub_eq_zero.1 h

/- English proof (translation)
Set `T : Set (Module.End ℂ (Sm E (r + s)))` to `Set.range fun kl : Fin s × Fin s => Eop (a := r + s) τ (Fin.natAdd r kl.1) (Fin.natAdd r kl.2)`. Establish `h1 : capR r s τ u ∈ Subalgebra.centralizer ℂ T`. Use `qdet_mem _ _ (fun i j => ?_) _` and prove the remaining obligations. Rewrite using `[Subalgebra.mem_centralizer_iff]`. Introduce and unpack `_ ⟨kl, rfl⟩`.

Conclude with `(Eop_commute_blocks r s τ i j kl.1 kl.2).symm.eq`. Establish `h2 : capS r s τ v ∈ Subalgebra.centralizer ℂ {capR r s τ u}`. Use `qdet_mem _ _ (fun k l => ?_) _` and prove the remaining obligations. Rewrite using `[Subalgebra.mem_centralizer_iff]`. Introduce and unpack `_ rfl`.

Conclude with `((Subalgebra.mem_centralizer_iff ℂ).1 h1 _ ⟨(k, l), rfl⟩).symm`. Conclude with `((Subalgebra.mem_centralizer_iff ℂ).1 h2 _ rfl)`.
-/
theorem capR_commute_capS (r s : ℕ) (τ : E →+* ℂ) (u v : ℂ) : Commute (capR r s τ u) (capS r s τ v) := by
  let T : Set (Module.End ℂ (Sm E (r + s))) :=
    Set.range fun kl : Fin s × Fin s => Eop (a := r + s) τ (Fin.natAdd r kl.1) (Fin.natAdd r kl.2)
  have h1 : capR r s τ u ∈ Subalgebra.centralizer ℂ T := by
    refine qdet_mem _ _ (fun i j => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨kl, rfl⟩
    exact (Eop_commute_blocks r s τ i j kl.1 kl.2).symm.eq
  have h2 : capS r s τ v ∈ Subalgebra.centralizer ℂ {capR r s τ u} := by
    refine qdet_mem _ _ (fun k l => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact ((Subalgebra.mem_centralizer_iff ℂ).1 h1 _ ⟨(k, l), rfl⟩).symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 h2 _ rfl)

/- English proof (translation)
Establish `h : ∑ i, n i = n 0 + n 1` using `two_sum n`. Set `S : Subalgebra ℂ (Module.End ℂ (Sm E (n 0 + n 1)))` to `Algebra.adjoin ℂ (Set.range fun pq : Fin (n 0 + n 1) × Fin (n 0 + n 1) => Eop τ pq.1 pq.2)`. Establish `hSE : ∀ p q, Eop τ p q ∈ S` using `fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩`. Establish `hSL : S ≤ GlobalTheory.SpehInfChar.leftInvAlg (unipRad (Ad E) (stdBlocks n h))` using `Algebra.adjoin_le (by rintro _ ⟨pq, rfl⟩; exact GlobalTheory.SpehInfChar.Eop_mem_leftInvAlg _ τ pq.1 pq.2)`. Set `X : Fin (n 0 + n 1) → Fin (n 0 + n 1) → S` to `fun p q => ⟨Eop τ p q, hSE p q⟩`.

Establish `hX : Formalism.REAL.GlRel X` using `fun a b c' d => Subtype.ext (by`. Use `glRel_Eop (a := n 0 + n 1) τ a b c' d` as an intermediate fact. Apply the tactic sequence `split_ifs at this ⊢ <;> simpa [X] using this)`. Establish `key` using `GlobalTheory.SpehInfChar.qdet_sub_blocks_mem S n h X hX u`. Establish `hB0 : Formalism.REAL.qdet (fun p q : Fin (n 0) => Eop (a` using `n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) (u + ((n 0 : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) 0 : ℂ) / 2) = capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) := by`.

Establish `e1 : (fun p q : Fin (n 0) => Eop (a` using `n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) = fun p q => Eop (a := n 0 + n 1) τ (Fin.castAdd (n 1) p) (Fin.castAdd (n 1) q) := by`. Use function extensionality and compare the values at `p q`. Rewrite using `[std_zero, std_zero]`. Rewrite using `[e1, modExp_zero, capR]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hB1 : Formalism.REAL.qdet (fun p q : Fin (n 1) => Eop (a` using `n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) (u + ((n 1 : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) 1 : ℂ) / 2) = capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) := by`. Establish `e1 : (fun p q : Fin (n 1) => Eop (a` using `n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) = fun p q => Eop (a := n 0 + n 1) τ (Fin.natAdd (n 0) p) (Fin.natAdd (n 0) q) := by`. Use function extensionality and compare the values at `p q`.

Rewrite using `[std_one, std_one]`. Rewrite using `[e1, modExp_one, capS]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hval : S.val (List.ofFn fun i : Fin 2 => Formalism.REAL.qdet (fun p q : Fin (n i) => X (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩)) (u + ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod = capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) * capS (n 0) (n 1) τ (u + (n 0 …`. Rewrite using `[map_list_prod, List.map_ofFn, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]`. Simplify using `only [Function.comp_apply, List.prod_cons, List.prod_nil, mul_one, Fin.succ_zero_eq_one]`. Rewrite using `[← hB0, ← hB1, map_qdet, map_qdet]`. Both sides reduce to the same expression.

Establish `hcap : S.val (Formalism.REAL.qdet X (u + (((n 0 + n 1 : ℕ) : ℂ) - 1) / 2)) = cap τ u`. Rewrite using `[map_qdet]`. Both sides reduce to the same expression. Establish `hψ : ∀ v ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, F.1 (v * g) = F.1 g` using `fun v hv g => by`. Take `⟨x, rfl⟩` from `exists_unip_of_mem n h hv`.

Conclude with `hF x g`. Rewrite using `[lev_eq_leviEmb n h m]`. Use `set ℓ := leviEmb (Ad E) (stdBlocks n h) (levPair m) with hℓ`. Set `L : S →ₗ[ℂ] ℂ` to `{ toFun := fun w => ((w : Module.End ℂ (Sm E (n 0 + n 1))) F).1 ℓ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hker : Submodule.span ℂ {y : S | ∃ (p q : Fin (n 0 + n 1)) (w : S), blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} ≤ LinearMap.ker L`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, q, w, hpq, rfl⟩`. Express the relevant statement in the definitionally equal form `(Eop τ p q ((w : Module.End ℂ (Sm E (n 0 + n 1))) F)).1 ℓ = 0`. Conclude with `GlobalTheory.SpehInfChar.Eop_leviEmb_eq_zero E n h _ (hSL w.2 F hψ) τ p q hpq _`. Establish `h1` using `hker key`.

Rewrite `h1` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`. Establish `hL : ∀ w : S, L w = ((S.val w) F).1 ℓ` using `fun _ => rfl`. Rewrite `h1` using `[hL, hL, hcap, hval]`. Rewrite using `[h1, (capR_commute_capS (n 0) (n 1) τ _ _).eq]`. Both sides reduce to the same expression.
-/
theorem capelli_levi_factorization (n : Fin 2 → ℕ) (τ : E →+* ℂ) (u : ℂ) (F : Sm E (n 0 + n 1))
    (hF : ∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) (g : GA E (n 0 + n 1)), F.1 (unip x * g) = F.1 g)
    (m : GA E (n 0) × GA E (n 1)) :
    (cap (a := n 0 + n 1) τ u F).1 (lev (Ad E) (n 0) (n 1) m) =
      (capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) F)).1
        (lev (Ad E) (n 0) (n 1) m) := by
  have h : ∑ i, n i = n 0 + n 1 := two_sum n
  let S : Subalgebra ℂ (Module.End ℂ (Sm E (n 0 + n 1))) :=
    Algebra.adjoin ℂ (Set.range fun pq : Fin (n 0 + n 1) × Fin (n 0 + n 1) => Eop τ pq.1 pq.2)
  have hSE : ∀ p q, Eop τ p q ∈ S := fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩
  have hSL : S ≤ GlobalTheory.SpehInfChar.leftInvAlg (unipRad (Ad E) (stdBlocks n h)) :=
    Algebra.adjoin_le (by rintro _ ⟨pq, rfl⟩; exact GlobalTheory.SpehInfChar.Eop_mem_leftInvAlg _ τ pq.1 pq.2)
  let X : Fin (n 0 + n 1) → Fin (n 0 + n 1) → S := fun p q => ⟨Eop τ p q, hSE p q⟩
  have hX : Formalism.REAL.GlRel X := fun a b c' d => Subtype.ext (by
    have := glRel_Eop (a := n 0 + n 1) τ a b c' d
    split_ifs at this ⊢ <;> simpa [X] using this)
  have key := GlobalTheory.SpehInfChar.qdet_sub_blocks_mem S n h X hX u
  have hB0 : Formalism.REAL.qdet (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩))
      (u + ((n 0 : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) 0 : ℂ) / 2) = capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) := by
    have e1 : (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) =
        fun p q => Eop (a := n 0 + n 1) τ (Fin.castAdd (n 1) p) (Fin.castAdd (n 1) q) := by
      funext p q
      rw [std_zero, std_zero]
    rw [e1, modExp_zero, capR]
    congr 1
    push_cast
    ring
  have hB1 : Formalism.REAL.qdet (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩))
      (u + ((n 1 : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) 1 : ℂ) / 2) = capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) := by
    have e1 : (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) =
        fun p q => Eop (a := n 0 + n 1) τ (Fin.natAdd (n 0) p) (Fin.natAdd (n 0) q) := by
      funext p q
      rw [std_one, std_one]
    rw [e1, modExp_one, capS]
    congr 1
    push_cast
    ring
  have hval : S.val (List.ofFn fun i : Fin 2 => Formalism.REAL.qdet (fun p q : Fin (n i) => X (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod =
      capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) * capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) := by
    rw [map_list_prod, List.map_ofFn, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    simp only [Function.comp_apply, List.prod_cons, List.prod_nil, mul_one, Fin.succ_zero_eq_one]
    rw [← hB0, ← hB1, map_qdet, map_qdet]
    rfl
  have hcap : S.val (Formalism.REAL.qdet X (u + (((n 0 + n 1 : ℕ) : ℂ) - 1) / 2)) = cap τ u := by
    rw [map_qdet]
    rfl
  have hψ : ∀ v ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, F.1 (v * g) = F.1 g := fun v hv g => by
    obtain ⟨x, rfl⟩ := exists_unip_of_mem n h hv
    exact hF x g
  rw [lev_eq_leviEmb n h m]
  set ℓ := leviEmb (Ad E) (stdBlocks n h) (levPair m) with hℓ
  let L : S →ₗ[ℂ] ℂ :=
    { toFun := fun w => ((w : Module.End ℂ (Sm E (n 0 + n 1))) F).1 ℓ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : Submodule.span ℂ {y : S | ∃ (p q : Fin (n 0 + n 1)) (w : S), blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} ≤
      LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, q, w, hpq, rfl⟩
    change (Eop τ p q ((w : Module.End ℂ (Sm E (n 0 + n 1))) F)).1 ℓ = 0
    exact GlobalTheory.SpehInfChar.Eop_leviEmb_eq_zero E n h _ (hSL w.2 F hψ) τ p q hpq _
  have h1 := hker key
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
  have hL : ∀ w : S, L w = ((S.val w) F).1 ℓ := fun _ => rfl
  rw [hL, hL, hcap, hval] at h1
  rw [h1, (capR_commute_capS (n 0) (n 1) τ _ _).eq]
  rfl

/- English proof (translation)
Introduce `E _ _ _ r s τ u F hF m`. Conclude with `capelli_levi_factorization ![r, s] τ u F hF m`.
-/
theorem cap_levi : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ)
    (F : Sm E (r + s)), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
    ∀ m : GA E r × GA E s, (cap (a := r + s) τ u F).1 (lev (Ad E) r s m) =
      (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) F)).1 (lev (Ad E) r s m) := by
  intro E _ _ _ r s τ u F hF m
  exact capelli_levi_factorization ![r, s] τ u F hF m

end GlobalTheory.CompanionTheory.CTFin.CapFactor

end
