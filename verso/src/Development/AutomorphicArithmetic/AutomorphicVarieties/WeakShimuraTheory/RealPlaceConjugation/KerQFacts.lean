import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Rewrite `hu`, `h`, the goal using `[KStar.TotallyRealRoots.mem_princ]`. Rewrite `h` using `[Units.val_pow_eq_pow_val]`. Use `set x : ℤ_[l] := (u : ℤ_[l]) with hx`. Use `set S : ℤ_[l] := ∑ i ∈ Finset.range (l - 1), x ^ i with hSdef`.

Establish `hgeom : x ^ (l - 1) - 1 = (x - 1) * S`. Rewrite using `[hSdef, mul_comm, geom_sum_mul]`. Establish `hl1 : (l : ℤ_[l]) ∣ x - 1` using `by simpa using hu`. Establish `hdiff : (l : ℤ_[l]) ∣ ∑ i ∈ Finset.range (l - 1), (x ^ i - 1)` using `Finset.dvd_sum fun i _ => dvd_trans hl1 (by simpa [one_pow] using sub_dvd_pow_sub_pow x 1 i)`. Establish `hSeq : S = ∑ i ∈ Finset.range (l - 1), (x ^ i - 1) + ((l : ℤ_[l]) - 1)`.

Rewrite using `[Finset.sum_sub_distrib, hSdef]`. Simplify using `[Nat.cast_sub hl.one_le]`. Establish `hlnu : ¬IsUnit (l : ℤ_[l])`. Rewrite using `[PadicInt.not_isUnit_iff, PadicInt.norm_p]`. Conclude with `inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)`.

Establish `hS : IsUnit S`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd]`. Apply `hlnu` to reduce the goal to its premises. Apply `isUnit_of_dvd_one` to reduce the goal to its premises.

Establish `h2` using `dvd_sub (dvd_add hdiff (dvd_refl (l : ℤ_[l]))) hne`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hSeq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[hgeom]`.

Conclude with `hS.dvd_mul_right.mp h`.
-/
private theorem mem_princ_of_pow {l : ℕ} [Fact l.Prime] {u : ℤ_[l]ˣ} (hu : u ∈ KStar.TotallyRealRoots.princ l 1) {n : ℕ}
    (h : u ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l n) : u ∈ KStar.TotallyRealRoots.princ l n := by
  have hl : l.Prime := Fact.out
  rw [KStar.TotallyRealRoots.mem_princ] at hu h ⊢
  rw [Units.val_pow_eq_pow_val] at h
  set x : ℤ_[l] := (u : ℤ_[l]) with hx
  set S : ℤ_[l] := ∑ i ∈ Finset.range (l - 1), x ^ i with hSdef
  have hgeom : x ^ (l - 1) - 1 = (x - 1) * S := by
    rw [hSdef, mul_comm, geom_sum_mul]
  have hl1 : (l : ℤ_[l]) ∣ x - 1 := by simpa using hu
  have hdiff : (l : ℤ_[l]) ∣ ∑ i ∈ Finset.range (l - 1), (x ^ i - 1) :=
    Finset.dvd_sum fun i _ => dvd_trans hl1 (by simpa [one_pow] using sub_dvd_pow_sub_pow x 1 i)
  have hSeq : S = ∑ i ∈ Finset.range (l - 1), (x ^ i - 1) + ((l : ℤ_[l]) - 1) := by
    rw [Finset.sum_sub_distrib, hSdef]
    simp [Nat.cast_sub hl.one_le]
  have hlnu : ¬IsUnit (l : ℤ_[l]) := by
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  have hS : IsUnit S := by
    by_contra hne
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd] at hne
    apply hlnu
    apply isUnit_of_dvd_one
    have h2 := dvd_sub (dvd_add hdiff (dvd_refl (l : ℤ_[l]))) hne
    convert h2 using 1
    rw [hSeq]
    ring
  rw [hgeom] at h
  exact hS.dvd_mul_right.mp h

/- English proof (translation)
Rewrite using `[commutator, Subgroup.commutator_le]`. Introduce `a _ b _`. Rewrite using `[MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, ← map_mul f a b, hf a b, map_mul, mul_assoc (f b), ← map_mul f a a⁻¹, mul_inv_cancel, map_one, mul_one, ← map_mul, mul_inv_cancel, map_one]`.
-/
private theorem comm_le_ker {Γ M : Type} [Group Γ] [Monoid M] (f : Γ →* M) (hf : ∀ a b, f (a * b) = f (b * a)) :
    commutator Γ ≤ f.ker := by
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, ← map_mul f a b, hf a b,
    map_mul, mul_assoc (f b), ← map_mul f a a⁻¹, mul_inv_cancel, map_one, mul_one, ← map_mul,
    mul_inv_cancel, map_one]

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD F hnf hab`. Use `haveI := hnf`. Use `haveI := hab`. Establish `hnorm : Normal ℚ F` using `by haveI : IsGalois ℚ F := IsAbelianGalois.toIsGalois`. Conclude with `IsGalois.to_normal`.

Take `⟨-, -, -, -, -, -, -, -, -, -, -, hrb, -, -⟩` from `UpperTheory.V.GradeZeroInterpolatingElement.facts D hD`. Establish `hcm : (cycMod ℚ Ω l 1).ker = Subgroup.comap (cycZ ℚ Ω l) (KStar.TotallyRealRoots.princ l 1)` using `rfl`. Establish `key : ∀ g, g ∈ (cycMod ℚ Ω l 1).ker ↔ cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l 1` using `fun g => by`. Rewrite using `[hcm]`. Both sides reduce to the same expression.

Establish `hdiag : ∀ g, D.rbar g = Matrix.diagonal fun i => IsLocalRing.residue c.O ((D.ps i g : (c.O)ˣ) : c.O)`. Introduce `g`. Use extensionality with `i j`. Simplify using `[Raw.rbar, Raw.r0, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hrc : ∀ a b, D.rbar (a * b) = D.rbar (b * a)`. Introduce `a b`. Rewrite using `[map_mul, map_mul, hdiag, hdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `mul_comm _ _`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show IsOpen ((F.fixingSubgroup ⊓ D.rbar.ker ⊓ (cycMod ℚ Ω l 1).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω))`. Rewrite using `[Subgroup.coe_inf, Subgroup.coe_inf, hcm, Subgroup.coe_comap]`. Conclude with `(F.fixingSubgroup_isOpen.inter hrb).inter ((KStar.TotallyRealRoots.isOpen_princ 1).preimage (continuous_cycZ ℚ Ω l))`.

Use `le_inf (le_inf ?_ ?_) ?_` and prove the remaining obligations. Rewrite using `[← @IntermediateField.restrictNormalHom_ker _ _ _ _ _ F hnorm]`. Conclude with `comm_le_ker _ fun a b => by`. Rewrite using `[map_mul, map_mul]`. Conclude with `(IsMulCommutative.is_comm (M := Gal(F/ℚ))).comm _ _`.

Conclude with `comm_le_ker _ hrc`. Conclude with `comm_le_ker _ fun a b => by rw [map_mul, map_mul, mul_comm]`. Introduce `m F' hL`. Prove the components needed by the constructor for the conclusion. Use extensionality with `g`.

Simplify using `only [kerQ, levU, Subgroup.mem_inf, Subgroup.mem_comap, key, hL g]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨⟨hF, hp⟩, hr⟩, h1⟩`. Conclude with `⟨⟨⟨hF, hr⟩, h1⟩, mem_princ_of_pow h1 hp⟩`. Introduce and unpack `⟨⟨⟨hF, hr⟩, h1⟩, hn⟩`.

Conclude with `⟨⟨⟨hF, Subgroup.pow_mem _ hn _⟩, hr⟩, h1⟩`. Introduce `g hg`. Simplify using `only [cycU, kerQ, Subgroup.mem_inf, MonoidHom.mem_ker] at hg`. Rewrite using `[hL g]`. Use `⟨hg.1.1.1, ?_⟩` and prove the remaining obligations.

Rewrite using `[hg.2, one_pow]`. Conclude with `one_mem _`.
-/
theorem UpperTheory.V.Ws.kerOverRationals_open_commutator_layer :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (F : IntermediateField ℚ Ω) [NumberField F] [IsAbelianGalois ℚ F], IsOpen (kerQ D F : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ kerQ D F ∧ ∀ (m : ℕ) (F' : IntermediateField ℚ Ω), IsLayer l m F F' → kerQ D F' = levU l (kerQ D F) (m + 1) ∧ cycU l (kerQ D F) ≤ F'.fixingSubgroup := by
  intro Ω _ _ _ l _ c D hD F hnf hab
  haveI := hnf
  haveI := hab
  have hnorm : Normal ℚ F := by
    haveI : IsGalois ℚ F := IsAbelianGalois.toIsGalois
    exact IsGalois.to_normal
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrb, -, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  have hcm : (cycMod ℚ Ω l 1).ker = Subgroup.comap (cycZ ℚ Ω l) (KStar.TotallyRealRoots.princ l 1) := rfl
  have key : ∀ g, g ∈ (cycMod ℚ Ω l 1).ker ↔ cycZ ℚ Ω l g ∈ KStar.TotallyRealRoots.princ l 1 := fun g => by
    rw [hcm]
    rfl
  have hdiag : ∀ g, D.rbar g = Matrix.diagonal fun i => IsLocalRing.residue c.O ((D.ps i g : (c.O)ˣ) : c.O) := by
    intro g
    ext i j
    simp [Raw.rbar, Raw.r0, UpperTheory.V.GradeZeroInterpolatingElement.mapRep, UpperTheory.V.GradeZeroInterpolatingElement.diagRep, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hrc : ∀ a b, D.rbar (a * b) = D.rbar (b * a) := by
    intro a b
    rw [map_mul, map_mul, hdiag, hdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  refine ⟨?_, ?_, ?_⟩
  · show IsOpen ((F.fixingSubgroup ⊓ D.rbar.ker ⊓ (cycMod ℚ Ω l 1).ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω))
    rw [Subgroup.coe_inf, Subgroup.coe_inf, hcm, Subgroup.coe_comap]
    exact (F.fixingSubgroup_isOpen.inter hrb).inter
      ((KStar.TotallyRealRoots.isOpen_princ 1).preimage (continuous_cycZ ℚ Ω l))
  · refine le_inf (le_inf ?_ ?_) ?_
    · rw [← @IntermediateField.restrictNormalHom_ker _ _ _ _ _ F hnorm]
      exact comm_le_ker _ fun a b => by
        rw [map_mul, map_mul]
        exact (IsMulCommutative.is_comm (M := Gal(F/ℚ))).comm _ _
    · exact comm_le_ker _ hrc
    · exact comm_le_ker _ fun a b => by rw [map_mul, map_mul, mul_comm]
  · intro m F' hL
    constructor
    · ext g
      simp only [kerQ, levU, Subgroup.mem_inf, Subgroup.mem_comap, key, hL g]
      constructor
      · rintro ⟨⟨⟨hF, hp⟩, hr⟩, h1⟩
        exact ⟨⟨⟨hF, hr⟩, h1⟩, mem_princ_of_pow h1 hp⟩
      · rintro ⟨⟨⟨hF, hr⟩, h1⟩, hn⟩
        exact ⟨⟨⟨hF, Subgroup.pow_mem _ hn _⟩, hr⟩, h1⟩
    · intro g hg
      simp only [cycU, kerQ, Subgroup.mem_inf, MonoidHom.mem_ker] at hg
      rw [hL g]
      refine ⟨hg.1.1.1, ?_⟩
      rw [hg.2, one_pow]
      exact one_mem _
