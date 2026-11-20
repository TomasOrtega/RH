import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Clifford
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtIneL
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Establish `hI : Ine (F` using `ℚ) A ≤ (galEmb ℚ K Ω).range := by`. Rewrite using `[range_galEmb, ← D.η_ker]`. Conclude with `((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).1`. Establish `hsur : ∀ u : ℤ_[l]ˣ, ∃ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F` using `ℚ) A ∧ cycZ K Ω l s = u := fun u => by`.

Take `⟨σ, hσ, hu⟩` from `GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u`. Take `⟨s, rfl⟩` from `hI hσ`. Conclude with `⟨s, hσ, hu⟩`. Assume the negation of the conclusion as `hg`. Take `⟨s, hs, hsg⟩` from `hsur (cycZ K Ω l g)`.

Establish `hs1 : φ s ≠ 1`. Introduce `h1`. Establish `: φ (g * s⁻¹) = 1` using `hφ (by`. Rewrite using `[MonoidHom.mem_ker, cycBar, MonoidHom.comp_apply, map_mul, map_inv, hsg, mul_inv_cancel, map_one])`. Rewrite `this` using `[map_mul, map_inv, h1, inv_one, mul_one]`.

Conclude with `hg this`. Establish `hu : IsUnit ((1 + l : ℕ) : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]`. Simplify using the standard rewrite rules. Take `⟨t, ht, htu⟩` from `hsur hu.unit`.

Establish `ht1 : D.ΨQ (galEmb ℚ K Ω t) ^ m = 1`. Distinguish the cases in `h1 : φ t = 1`. Establish `h2` using `h (s * t) (by rw [map_mul]; exact mul_mem hs ht) (by rwa [map_mul, h1, mul_one])`. Rewrite `h2` using `[map_mul, map_mul, mul_pow, h s hs hs1, one_mul]`. Then use the resulting hypothesis. Conclude with `h t ht h1`.

Establish `hn : Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ = 1`. Rewrite using `[Chr.dirG, MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one]`. Establish `hc : (chiO ℚ Ω l c.O (galEmb ℚ K Ω t) : c.O) = ((1 + l : ℕ) : c.O)`. Establish `: cycZ ℚ Ω l (galEmb ℚ K Ω t) = hu.unit` using `htu`. Rewrite using `[chiO, MonoidHom.comp_apply, this]`.

Simplify using the standard rewrite rules. Establish `h3 : ((D.Ψ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ : c.Oˣ) : c.O) = ((1 + l : ℕ) : c.O) ^ (e * Nat.card (ZMod N)ˣ)`. Rewrite using `[Dat.Ψ, Chr.Psi, MonoidHom.mul_apply, mul_pow, hn, mul_one, zpow_natCast, MonoidHom.pow_apply, ← pow_mul, Units.val_pow_eq_pow_val, hc]`. Establish `h4 : ((D.ΨQ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ : (PadicAlgCl l)ˣ) : PadicAlgCl l) = ((1 + l : ℕ) : PadicAlgCl l) ^ (e * Nat.card (ZMod N)ˣ)`. Use `congrArg (algebraMap c.O (PadicAlgCl l)) h3` as an intermediate fact.

Rewrite `this` using `[map_pow, map_natCast]`. Rewrite using `[← this, Dat.ΨQ, MonoidHom.comp_apply, ← map_pow]`. Both sides reduce to the same expression. Establish `h5 : ((1 + l : ℕ) : PadicAlgCl l) ^ (e * Nat.card (ZMod N)ˣ * m) = 1`. Rewrite using `[pow_mul, ← h4, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, ht1, one_pow, Units.val_one]`.

Establish `h6 : (1 + l) ^ (e * Nat.card (ZMod N)ˣ * m) = 1` using `by exact_mod_cast h5`. Establish `he` using `D.gd.e_pos`. Establish `hN : 0 < Nat.card (ZMod N)ˣ` using `Nat.card_pos`. Break down `Nat.pow_eq_one.1 h6 with h7 | h7` into its components or cases. Conclude with `hl.ne_zero (by omega)`.

Conclude with `(mul_ne_zero (mul_ne_zero (by omega) hN.ne') hm) h7`.
-/
private theorem twist_triv {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
    (D : Dat Ω K c e ψ) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) {C : Type} [Group C]
    (φ : G K Ω →* C) (hφ : (cycBar K Ω l).ker ≤ φ.ker) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A → φ s ≠ 1 → D.ΨQ (galEmb ℚ K Ω s) ^ m = 1) (g : G K Ω) :
    φ g = 1 := by
  have hl : l.Prime := Fact.out
  have hI : Ine (F := ℚ) A ≤ (galEmb ℚ K Ω).range := by
    rw [range_galEmb, ← D.η_ker]
    exact ((dat_facts D).2.2.2.2.2.2.2.2.2.2 A hA).1
  have hsur : ∀ u : ℤ_[l]ˣ, ∃ s : G K Ω, galEmb ℚ K Ω s ∈ Ine (F := ℚ) A ∧ cycZ K Ω l s = u := fun u => by
    obtain ⟨σ, hσ, hu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
    obtain ⟨s, rfl⟩ := hI hσ
    exact ⟨s, hσ, hu⟩
  by_contra hg
  obtain ⟨s, hs, hsg⟩ := hsur (cycZ K Ω l g)
  have hs1 : φ s ≠ 1 := by
    intro h1
    have : φ (g * s⁻¹) = 1 := hφ (by
      rw [MonoidHom.mem_ker, cycBar, MonoidHom.comp_apply, map_mul, map_inv, hsg, mul_inv_cancel, map_one])
    rw [map_mul, map_inv, h1, inv_one, mul_one] at this
    exact hg this
  have hu : IsUnit ((1 + l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  obtain ⟨t, ht, htu⟩ := hsur hu.unit
  have ht1 : D.ΨQ (galEmb ℚ K Ω t) ^ m = 1 := by
    by_cases h1 : φ t = 1
    · have h2 := h (s * t) (by rw [map_mul]; exact mul_mem hs ht) (by rwa [map_mul, h1, mul_one])
      rwa [map_mul, map_mul, mul_pow, h s hs hs1, one_mul] at h2
    · exact h t ht h1
  have hn : Chr.dirG ℚ Ω ψ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ = 1 := by
    rw [Chr.dirG, MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one]
  have hc : (chiO ℚ Ω l c.O (galEmb ℚ K Ω t) : c.O) = ((1 + l : ℕ) : c.O) := by
    have : cycZ ℚ Ω l (galEmb ℚ K Ω t) = hu.unit := htu
    rw [chiO, MonoidHom.comp_apply, this]
    simp
  have h3 : ((D.Ψ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ : c.Oˣ) : c.O) = ((1 + l : ℕ) : c.O) ^ (e * Nat.card (ZMod N)ˣ) := by
    rw [Dat.Ψ, Chr.Psi, MonoidHom.mul_apply, mul_pow, hn, mul_one, zpow_natCast, MonoidHom.pow_apply, ← pow_mul,
      Units.val_pow_eq_pow_val, hc]
  have h4 : ((D.ΨQ (galEmb ℚ K Ω t) ^ Nat.card (ZMod N)ˣ : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      ((1 + l : ℕ) : PadicAlgCl l) ^ (e * Nat.card (ZMod N)ˣ) := by
    have := congrArg (algebraMap c.O (PadicAlgCl l)) h3
    rw [map_pow, map_natCast] at this
    rw [← this, Dat.ΨQ, MonoidHom.comp_apply, ← map_pow]
    rfl
  have h5 : ((1 + l : ℕ) : PadicAlgCl l) ^ (e * Nat.card (ZMod N)ˣ * m) = 1 := by
    rw [pow_mul, ← h4, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, ht1, one_pow, Units.val_one]
  have h6 : (1 + l) ^ (e * Nat.card (ZMod N)ˣ * m) = 1 := by exact_mod_cast h5
  have he := D.gd.e_pos
  have hN : 0 < Nat.card (ZMod N)ˣ := Nat.card_pos
  rcases Nat.pow_eq_one.1 h6 with h7 | h7
  · exact hl.ne_zero (by omega)
  · exact (mul_ne_zero (mul_ne_zero (by omega) hN.ne') hm) h7

/- English proof (translation)
Introduce `hC Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hg r h hI`. Establish `hirr : MatIrr ⊤ fun g => (D.rhoK r h.mult g : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))`. Introduce `W hW`. Use `hI W fun g hg v hv => ?_` and prove the remaining obligations. Rewrite `hg` using `[D.η_ker, ← range_galEmb]`.

Take `⟨s, rfl⟩` from `hg`. Conclude with `hW s trivial v hv`. Establish `key : MatIrr (cycBar K Ω l).ker fun g => (D.rhoK r h.mult g : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))`. Assume the negation of the conclusion as `hred`. Take `⟨φ, hφ1, hker, -, M, hM⟩` from `exists_selfTwist (D.rhoK r h.mult) (cycBar K Ω l).ker (fun a b => by simp [MonoidHom.mem_ker, mul_comm (cycBar K Ω l a)]) hirr hred`.

Take `⟨A, hA⟩` from `(Chr.placesQ Ω).1 l Fact.out`. Use `hφ1 (MonoidHom.ext (twist_triv D A hA φ hker 3 (by norm_num) fun s hs h1 => ?_))` and prove the remaining obligations. Establish `hch` using `(pt_inertia_above hC D hg h A hA).1 _ hs`. Establish `htr : (D.rhoK r h.mult s : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)).trace = (r0 D.η D.ΨQ (galEmb ℚ K Ω s)).mat.trace`. Rewrite using `[Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, ← hch]`.

Both sides reduce to the same expression. Establish `h2` using `congrArg (fun X => (X * ((M⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).trace) (hM s trivial)`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul] at h2`. Rewrite `h2` using `[Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, htr, smul_eq_mul]`. Establish `h3 : (r0 D.η D.ΨQ (galEmb ℚ K Ω s)).mat.trace = 0`.

Assume the negation of the conclusion as `h0`. Conclude with `h1 (Units.ext (mul_right_cancel₀ h0 (h2.trans (one_mul _).symm)))`. Rewrite `h3` using `[GG.mat, unitaryThreeReflection_left, tor_val, Matrix.trace_diagonal, Fin.sum_univ_three]`. Generalize the expression as in `D.ΨQ (galEmb ℚ K Ω s) = a at h3 ⊢`. Establish `h4 : (a : PadicAlgCl l) + 1 + (a : PadicAlgCl l)⁻¹ = 0` using `by simpa [wt1] using h3`.

Establish `ha : (a : PadicAlgCl l) * (a : PadicAlgCl l)⁻¹ = 1` using `mul_inv_cancel₀ a.ne_zero`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, Units.val_one]`. Take the linear combination `(a : PadicAlgCl l) * (a - 1) * h4 - ((a : PadicAlgCl l) - 1) * ha`. Use `⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => key W fun g hg v hv => hW ⟨g, hg⟩ v hv⟩` and prove the remaining obligations.
-/
theorem UpperTheory.V.U3.typeI_irr_cyc :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r),
      TypeI D.η r → Af.IsIrr ((D.rhoK r h.mult).comp (cycBar K Ω l).ker.subtype) := by
  intro hC Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hg r h hI
  have hirr : MatIrr ⊤ fun g => (D.rhoK r h.mult g : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) := by
    intro W hW
    refine hI W fun g hg v hv => ?_
    rw [D.η_ker, ← range_galEmb] at hg
    obtain ⟨s, rfl⟩ := hg
    exact hW s trivial v hv
  have key : MatIrr (cycBar K Ω l).ker fun g => (D.rhoK r h.mult g : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) := by
    by_contra hred
    obtain ⟨φ, hφ1, hker, -, M, hM⟩ := exists_selfTwist (D.rhoK r h.mult) (cycBar K Ω l).ker
      (fun a b => by simp [MonoidHom.mem_ker, mul_comm (cycBar K Ω l a)]) hirr hred
    obtain ⟨A, hA⟩ := (Chr.placesQ Ω).1 l Fact.out
    refine hφ1 (MonoidHom.ext (twist_triv D A hA φ hker 3 (by norm_num) fun s hs h1 => ?_))
    have hch := (pt_inertia_above hC D hg h A hA).1 _ hs
    have htr : (D.rhoK r h.mult s : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)).trace =
        (r0 D.η D.ΨQ (galEmb ℚ K Ω s)).mat.trace := by
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, ← hch]
      rfl
    have h2 := congrArg (fun X => (X * ((M⁻¹ : GL (Fin 3) (PadicAlgCl l)) : Matrix (Fin 3) (Fin 3) (PadicAlgCl l))).trace)
      (hM s trivial)
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul] at h2
    rw [Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, htr,
      smul_eq_mul] at h2
    have h3 : (r0 D.η D.ΨQ (galEmb ℚ K Ω s)).mat.trace = 0 := by
      by_contra h0
      exact h1 (Units.ext (mul_right_cancel₀ h0 (h2.trans (one_mul _).symm)))
    rw [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.trace_diagonal, Fin.sum_univ_three] at h3
    generalize D.ΨQ (galEmb ℚ K Ω s) = a at h3 ⊢
    have h4 : (a : PadicAlgCl l) + 1 + (a : PadicAlgCl l)⁻¹ = 0 := by simpa [wt1] using h3
    have ha : (a : PadicAlgCl l) * (a : PadicAlgCl l)⁻¹ = 1 := mul_inv_cancel₀ a.ne_zero
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    linear_combination (a : PadicAlgCl l) * (a - 1) * h4 - ((a : PadicAlgCl l) - 1) * ha
  refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => key W fun g hg v hv => hW ⟨g, hg⟩ v hv⟩
