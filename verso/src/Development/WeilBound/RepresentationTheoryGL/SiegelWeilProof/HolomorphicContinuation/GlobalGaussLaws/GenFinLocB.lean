import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocA

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

/- English proof (translation)
Take `⟨u, hu⟩` from `h`. Establish `h' : IsUnit (M.map f).det` using `by rw [← det_map, ← hu]; exact (u.isUnit.map f)`. Rewrite using `[Matrix.inv_def, Matrix.inv_def, ← det_map, ← hu, Ring.inverse_unit, Matrix.map_smul' _ _ _ (fun a b => map_mul f a b)]`. Establish `hadj : M.adjugate.map f = (M.map f).adjugate` using `RingHom.map_adjugate f M`. Establish `hinv : Ring.inverse (f ↑u) = f ↑u⁻¹`.

Rewrite using `[show f ↑u = ((Units.map f.toMonoidHom u : Sˣ) : S) from rfl, Ring.inverse_unit]`. Both sides reduce to the same expression. Rewrite using `[hadj, hinv]`.
-/
theorem map_nonsing_inv (f : R →+* S) (M : Matrix (Fin n) (Fin n) R) (h : IsUnit M.det) :
    (M⁻¹).map f = (M.map f)⁻¹ := by
  obtain ⟨u, hu⟩ := h
  have h' : IsUnit (M.map f).det := by rw [← det_map, ← hu]; exact (u.isUnit.map f)
  rw [Matrix.inv_def, Matrix.inv_def, ← det_map, ← hu, Ring.inverse_unit, Matrix.map_smul' _ _ _ (fun a b => map_mul f a b)]
  have hadj : M.adjugate.map f = (M.map f).adjugate := RingHom.map_adjugate f M
  have hinv : Ring.inverse (f ↑u) = f ↑u⁻¹ := by
    rw [show f ↑u = ((Units.map f.toMonoidHom u : Sˣ) : S) from rfl, Ring.inverse_unit]; rfl
  rw [hadj, hinv]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bf_cT (σ : R →+* R) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    bf (Formalism.UG.cT σ M) = Formalism.UG.cT σ (bf M) := rfl

/- English proof (translation)
Unfold `Formalism.UG.cT`. Rewrite using `[fromBlocks_map, fromBlocks_transpose]`.
-/
theorem cT_fromBlocks (σ : R →+* R) (A B C D : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (fromBlocks A B C D) =
      fromBlocks (Formalism.UG.cT σ A) (Formalism.UG.cT σ C) (Formalism.UG.cT σ B) (Formalism.UG.cT σ D) := by
  unfold Formalism.UG.cT; rw [fromBlocks_map, fromBlocks_transpose]

def Uni (σ : R →+* R) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Prop := Formalism.UG.cT σ M * J2 R n * M = J2 R n

/- English proof (translation)
Unfold `Uni at *`. Rewrite using `[Formalism.UG.cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J2 R n := by rw [hM, hN]`.
-/
theorem Uni.mul {σ : R →+* R} {M N : Matrix (Fin (n + n)) (Fin (n + n)) R} (hM : Uni σ M) (hN : Uni σ N) :
    Uni σ (M * N) := by
  unfold Uni at *
  rw [Formalism.UG.cT_mul]
  calc Formalism.UG.cT σ N * Formalism.UG.cT σ M * J2 R n * (M * N) = Formalism.UG.cT σ N * (Formalism.UG.cT σ M * J2 R n * M) * N := by
        simp only [Matrix.mul_assoc]
    _ = J2 R n := by rw [hM, hN]

/- English proof (translation)
Use `letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪`. Establish `hle : 𝔪 ≤ 𝔪.comap σ` using `hfix.symm ▸ le_refl _`. Set `σb : R ⧸ 𝔪 →+* R ⧸ 𝔪` to `Ideal.quotientMap 𝔪 σ hle`. Establish `hπσ : ∀ x, Ideal.Quotient.mk 𝔪 (σ x) = σb (Ideal.Quotient.mk 𝔪 x)` using `fun x => (Ideal.quotientMap_mk ..).symm`. Establish `hσb : ∀ x, σb (σb x) = x`.

Introduce `x`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[← hπσ, ← hπσ, hσ]`. Establish `hdet : IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det` using `by rw [← det_map]; exact hgu.map _`. Set `gb : GL (Fin (n + n)) (R ⧸ 𝔪)` to `Matrix.nonsingInvUnit _ hdet`.

Establish `hgb : gb ∈ Formalism.UG.UJ σb (J2 (R ⧸ 𝔪) n)` using `by show Formalism.UG.cT σb (g.map (Ideal.Quotient.mk 𝔪)) * J2 (R ⧸ 𝔪) n * g.map (Ideal.Quotient.mk 𝔪) = J2 (R ⧸ 𝔪) n`. Use `congrArg (fun M => M.map (Ideal.Quotient.mk 𝔪)) hg` as an intermediate fact. Simplify using `only [Matrix.map_mul, standard_symplectic_matrix_map] at this`. Rewrite `this` using `[cT_map σ σb _ hπσ]`. Then use the resulting hypothesis. Take `⟨I, hI⟩` from `hF (R ⧸ 𝔪) σb hσb n gb hgb`.

Use `⟨I, isUnit_of σ 𝔪 horb _ ?_ ?_⟩` and prove the remaining obligations. Introduce `hm`. Establish `h0 : Ideal.Quotient.mk 𝔪 (blkDm (g * wIm I)).det = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 hm`. Rewrite `h0` using `[det_map, blkDm_map, Matrix.map_mul, wIm_map]`. Conclude with `hI.ne_zero h0`.

Introduce `hm`. Establish `: (blkDm (g * wIm I)).det ∈ 𝔪.comap σ` using `hm`. Rewrite `this` using `[hfix]`. Establish `h0 : Ideal.Quotient.mk 𝔪 (blkDm (g * wIm I)).det = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 this`. Rewrite `h0` using `[det_map, blkDm_map, Matrix.map_mul, wIm_map]`.

Conclude with `hI.ne_zero h0`.
-/
theorem caseA (hF : LocRedField) (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal]
    (hfix : 𝔪.comap σ = 𝔪) (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (g : Matrix (Fin (n + n)) (Fin (n + n)) R) (hg : Uni σ g) (hgu : IsUnit g.det) :
    ∃ I : Finset (Fin n), IsUnit (blkDm (g * wIm I)).det := by
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hle : 𝔪 ≤ 𝔪.comap σ := hfix.symm ▸ le_refl _
  let σb : R ⧸ 𝔪 →+* R ⧸ 𝔪 := Ideal.quotientMap 𝔪 σ hle
  have hπσ : ∀ x, Ideal.Quotient.mk 𝔪 (σ x) = σb (Ideal.Quotient.mk 𝔪 x) := fun x => (Ideal.quotientMap_mk ..).symm
  have hσb : ∀ x, σb (σb x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← hπσ, ← hπσ, hσ]
  have hdet : IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det := by rw [← det_map]; exact hgu.map _
  let gb : GL (Fin (n + n)) (R ⧸ 𝔪) := Matrix.nonsingInvUnit _ hdet
  have hgb : gb ∈ Formalism.UG.UJ σb (J2 (R ⧸ 𝔪) n) := by
    show Formalism.UG.cT σb (g.map (Ideal.Quotient.mk 𝔪)) * J2 (R ⧸ 𝔪) n * g.map (Ideal.Quotient.mk 𝔪) = J2 (R ⧸ 𝔪) n
    have := congrArg (fun M => M.map (Ideal.Quotient.mk 𝔪)) hg
    simp only [Matrix.map_mul, standard_symplectic_matrix_map] at this
    rwa [cT_map σ σb _ hπσ] at this
  obtain ⟨I, hI⟩ := hF (R ⧸ 𝔪) σb hσb n gb hgb
  refine ⟨I, isUnit_of σ 𝔪 horb _ ?_ ?_⟩
  · intro hm
    have h0 : Ideal.Quotient.mk 𝔪 (blkDm (g * wIm I)).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [det_map, blkDm_map, Matrix.map_mul, wIm_map] at h0
    exact hI.ne_zero h0
  · intro hm
    have : (blkDm (g * wIm I)).det ∈ 𝔪.comap σ := hm
    rw [hfix] at this
    have h0 : Ideal.Quotient.mk 𝔪 (blkDm (g * wIm I)).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 this
    rw [det_map, blkDm_map, Matrix.map_mul, wIm_map] at h0
    exact hI.ne_zero h0

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
