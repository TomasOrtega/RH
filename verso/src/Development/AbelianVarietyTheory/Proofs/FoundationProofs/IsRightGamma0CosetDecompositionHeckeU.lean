import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.RightRepU

/- English proof (translation)
Simplify using `[repL, Matrix.adjugate_fin_two_of]`.
-/
lemma adj_repL (L l : ℕ) (j : Fin l) :
    (repL L l (some j)).adjugate = !![(1:ℤ), 0; -((L:ℤ) * ((j:ℕ):ℤ)), (l:ℤ)] := by
  simp [repL, Matrix.adjugate_fin_two_of]

/- English proof (translation)
The claim follows from `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 γ.2)`.
-/
lemma dvd_10 {L : ℕ} (γ : Gamma0 L) : (L:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (Gamma0_mem.1 γ.2)

/- English proof (translation)
Introduce `h`. Establish `hdet` using `Matrix.SpecialLinearGroup.det_coe (γ : SL(2,ℤ))`. Rewrite `hdet` using `[Matrix.det_fin_two]`. Establish `hc' : (l:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 1 0` using `dvd_trans (Int.natCast_dvd_natCast.2 hlL) (dvd_10 γ)`. Establish `h1 : (l:ℤ) ∣ 1`.

Rewrite using `[← hdet]`. Conclude with `dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right hc' _)`. Use `Int.eq_one_of_dvd_one (by positivity) h1` as an intermediate fact. Conclude with `hl.one_lt.ne' (by exact_mod_cast this)`.
-/
lemma not_dvd_00 {L l : ℕ} (hl : l.Prime) (hlL : l ∣ L) (γ : Gamma0 L) :
    ¬ (l:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 0 0 := by
  intro h
  have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2,ℤ))
  rw [Matrix.det_fin_two] at hdet
  have hc' : (l:ℤ) ∣ ((γ : SL(2,ℤ)) : M2) 1 0 := dvd_trans (Int.natCast_dvd_natCast.2 hlL) (dvd_10 γ)
  have h1 : (l:ℤ) ∣ 1 := by
    rw [← hdet]; exact dvd_sub (dvd_mul_of_dvd_left h _) (dvd_mul_of_dvd_right hc' _)
  have := Int.eq_one_of_dvd_one (by positivity) h1
  exact hl.one_lt.ne' (by exact_mod_cast this)

end GlobalTheory.EisM.RightRepU

namespace GlobalTheory.EisM.RightRepU

/- English proof (translation)
Use `haveI := Fact.mk hl`. Use `haveI : NeZero l := ⟨hl.ne_zero⟩`. Establish `hpr : Prime (l:ℤ)` using `Nat.prime_iff_prime_int.mp hl`. Establish `hlpos : (0:ℤ) < l` using `by exact_mod_cast hl.pos`. Simplify using `only [RRep, adj_repL]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨j, γ⟩ -`. Establish `hdet` using `Matrix.SpecialLinearGroup.det_coe (γ : SL(2,ℤ))`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.det_mul]`.

Rewrite using `[hdet, Matrix.det_fin_two_of]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Conclude with `dvd_add (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)) (dvd_mul_of_dvd_right (dvd_10 γ) _)`. Simplify `not_dvd_00 hl hlL γ` using `[Matrix.mul_apply, Fin.sum_univ_two]`.

Introduce and unpack `⟨j, γ⟩ - ⟨j', γ'⟩ - h`. Simplify using `only at h`. Establish `e` using `fun r s => congrArg (fun M : M2 => M r s) h`. Establish `h00` using `e 0 0`. Establish `h01` using `e 0 1`.

Establish `h10` using `e 1 0`. Establish `h11` using `e 1 1`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11`. Take `⟨c1, hc1⟩` from `dvd_10 γ`. Take `⟨c1', hc1'⟩` from `dvd_10 γ'`.

Establish `hLz : (0:ℤ) < L` using `by exact_mod_cast hL`. Establish `hk : (L:ℤ) * ((((j':ℕ):ℤ) - (j:ℕ)) * ((γ : SL(2,ℤ)) : M2) 0 0) = (L:ℤ) * ((l:ℤ) * (c1' - c1))`. Rewrite `h10` using `[hc1, hc1', ← h00]`. Take the linear combination `h10`. Establish `hk2` using `mul_left_cancel₀ hLz.ne' hk`.

Establish `hdv : (l:ℤ) ∣ (((j':ℕ):ℤ) - (j:ℕ)) * ((γ : SL(2,ℤ)) : M2) 0 0` using `⟨_, hk2⟩`. Establish `hjj` using `(hpr.dvd_or_dvd hdv).resolve_right (not_dvd_00 hl hlL γ)`. Establish `hj0 : ((j':ℕ):ℤ) - (j:ℕ) = 0`. Apply `Int.eq_zero_of_abs_lt_dvd hjj` to reduce the goal to its premises. Use `j.isLt` as an intermediate fact.

Use `j'.isLt` as an intermediate fact. Apply the tactic sequence `rw [abs_lt]; constructor <;> omega`. Establish `hjeq : j = j'` using `Fin.ext (by omega)`. Substitute `hjeq` using the available equality. Establish `h10' : ((γ : SL(2,ℤ)) : M2) 1 0 = ((γ' : SL(2,ℤ)) : M2) 1 0`.

Rewrite `h10` using `[← h00]`. Conclude with `mul_left_cancel₀ hlpos.ne' (by linear_combination h10)`. Establish `h11' : ((γ : SL(2,ℤ)) : M2) 1 1 = ((γ' : SL(2,ℤ)) : M2) 1 1`. Rewrite `h11` using `[← h01]`. Conclude with `mul_left_cancel₀ hlpos.ne' (by linear_combination h11)`.

Use `Prod.ext rfl (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ (fun r s => ?_)))` and prove the remaining obligations. Apply the tactic sequence `fin_cases r <;> fin_cases s`. Conclude with `h00`. Conclude with `h01`. Conclude with `h10'`.

Conclude with `h11'`. Introduce and unpack `δ ⟨hdet, hc, ha⟩`. Rewrite `hdet` using `[Matrix.det_fin_two]`. Take `⟨c1, hc1⟩` from `hc`. Take `⟨L1, hL1⟩` from `hlL`.

Establish `hLl : (L:ℤ) = l * L1` using `by rw [hL1]; push_cast; ring`. Establish `hd : (l:ℤ) ∣ δ 1 1`. Establish `: (l:ℤ) ∣ δ 0 0 * δ 1 1` using `⟨1 + L1 * c1 * δ 0 1, by linear_combination hdet + δ 0 1 * hc1 + δ 0 1 * c1 * hLl⟩`. Conclude with `(hpr.dvd_or_dvd this).resolve_left ha`. Take `⟨d1, hd1⟩` from `hd`.

Establish `ha0 : ((δ 0 0 : ℤ) : ZMod l) ≠ 0`. Rewrite using `[Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]` and apply the resulting hypothesis. Take `⟨x, hx⟩ : ∃ x : ZMod l, x = -(c1 : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹` from `⟨_, rfl⟩`. Set `j : Fin l` to `⟨x.val, ZMod.val_lt x⟩`. Establish `hj : (l:ℤ) ∣ c1 + ((j:ℕ):ℤ) * δ 0 0`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Simplify using `only [j, ZMod.natCast_val, ZMod.cast_id', id]`. Rewrite using `[hx, mul_assoc, inv_mul_cancel₀ ha0]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨m, hm⟩` from `hj`. Set `M : M2` to `!![δ 0 0, δ 0 1; (L:ℤ) * m, d1 + L1 * ((j:ℕ):ℤ) * δ 0 1]`. Establish `hM : M.det = 1`. Rewrite using `[Matrix.det_fin_two_of]`. Apply `mul_left_cancel₀ hlpos.ne'` to reduce the goal to its premises.

Take the linear combination `hdet + δ 0 1 * hc1 + δ 0 1 * L * hm - ((j:ℕ):ℤ) * δ 0 0 * δ 0 1 * hLl - δ 0 0 * hd1`. Set `g : SL(2,ℤ)` to `⟨M, hM⟩`. Establish `hmem : g ∈ Gamma0 L`. Rewrite using `[Gamma0_mem]`. Simplify using `[g, M]`.

Use `⟨(j, ⟨g, hmem⟩), trivial, ?_⟩` and prove the remaining obligations. Use extensionality with `r s`. Apply the tactic sequence `fin_cases r <;> fin_cases s`. Simplify using `[g, M, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify using `[g, M, Matrix.mul_apply, Fin.sum_univ_two]`.

Simplify using `[g, M, Matrix.mul_apply, Fin.sum_univ_two]`. Take the linear combination `-(L:ℤ) * hm - hc1`. Simplify using `[g, M, Matrix.mul_apply, Fin.sum_univ_two]`. Take the linear combination `-hd1 - ((j:ℕ):ℤ) * δ 0 1 * hLl`.
-/
theorem rrep (L l : ℕ) (hl : l.Prime) (hlL : l ∣ L) (hL : 0 < L) :
    RRep L (DU L l) (fun j : Fin l => (repL L l (some j)).adjugate) := by
  haveI := Fact.mk hl
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hpr : Prime (l:ℤ) := Nat.prime_iff_prime_int.mp hl
  have hlpos : (0:ℤ) < l := by exact_mod_cast hl.pos
  simp only [RRep, adj_repL]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨j, γ⟩ -
    have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2,ℤ))
    refine ⟨?_, ?_, ?_⟩
    · simp only [Matrix.det_mul]
      rw [hdet, Matrix.det_fin_two_of]; ring
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      exact dvd_add (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)) (dvd_mul_of_dvd_right (dvd_10 γ) _)
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using not_dvd_00 hl hlL γ
  · rintro ⟨j, γ⟩ - ⟨j', γ'⟩ - h
    simp only at h
    have e := fun r s => congrArg (fun M : M2 => M r s) h
    have h00 := e 0 0
    have h01 := e 0 1
    have h10 := e 1 0
    have h11 := e 1 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    obtain ⟨c1, hc1⟩ := dvd_10 γ
    obtain ⟨c1', hc1'⟩ := dvd_10 γ'
    have hLz : (0:ℤ) < L := by exact_mod_cast hL
    have hk : (L:ℤ) * ((((j':ℕ):ℤ) - (j:ℕ)) * ((γ : SL(2,ℤ)) : M2) 0 0) = (L:ℤ) * ((l:ℤ) * (c1' - c1)) := by
      rw [hc1, hc1', ← h00] at h10
      linear_combination h10
    have hk2 := mul_left_cancel₀ hLz.ne' hk
    have hdv : (l:ℤ) ∣ (((j':ℕ):ℤ) - (j:ℕ)) * ((γ : SL(2,ℤ)) : M2) 0 0 := ⟨_, hk2⟩
    have hjj := (hpr.dvd_or_dvd hdv).resolve_right (not_dvd_00 hl hlL γ)
    have hj0 : ((j':ℕ):ℤ) - (j:ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd hjj
      have := j.isLt; have := j'.isLt
      rw [abs_lt]; constructor <;> omega
    have hjeq : j = j' := Fin.ext (by omega)
    subst hjeq
    have h10' : ((γ : SL(2,ℤ)) : M2) 1 0 = ((γ' : SL(2,ℤ)) : M2) 1 0 := by
      rw [← h00] at h10
      exact mul_left_cancel₀ hlpos.ne' (by linear_combination h10)
    have h11' : ((γ : SL(2,ℤ)) : M2) 1 1 = ((γ' : SL(2,ℤ)) : M2) 1 1 := by
      rw [← h01] at h11
      exact mul_left_cancel₀ hlpos.ne' (by linear_combination h11)
    refine Prod.ext rfl (Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ (fun r s => ?_)))
    fin_cases r <;> fin_cases s
    · exact h00
    · exact h01
    · exact h10'
    · exact h11'
  · rintro δ ⟨hdet, hc, ha⟩
    rw [Matrix.det_fin_two] at hdet
    obtain ⟨c1, hc1⟩ := hc
    obtain ⟨L1, hL1⟩ := hlL
    have hLl : (L:ℤ) = l * L1 := by rw [hL1]; push_cast; ring
    have hd : (l:ℤ) ∣ δ 1 1 := by
      have : (l:ℤ) ∣ δ 0 0 * δ 1 1 :=
        ⟨1 + L1 * c1 * δ 0 1, by linear_combination hdet + δ 0 1 * hc1 + δ 0 1 * c1 * hLl⟩
      exact (hpr.dvd_or_dvd this).resolve_left ha
    obtain ⟨d1, hd1⟩ := hd
    have ha0 : ((δ 0 0 : ℤ) : ZMod l) ≠ 0 := by
      rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨x, hx⟩ : ∃ x : ZMod l, x = -(c1 : ZMod l) * ((δ 0 0 : ℤ) : ZMod l)⁻¹ := ⟨_, rfl⟩
    let j : Fin l := ⟨x.val, ZMod.val_lt x⟩
    have hj : (l:ℤ) ∣ c1 + ((j:ℕ):ℤ) * δ 0 0 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [j, ZMod.natCast_val, ZMod.cast_id', id]
      rw [hx, mul_assoc, inv_mul_cancel₀ ha0]; ring
    obtain ⟨m, hm⟩ := hj
    let M : M2 := !![δ 0 0, δ 0 1; (L:ℤ) * m, d1 + L1 * ((j:ℕ):ℤ) * δ 0 1]
    have hM : M.det = 1 := by
      rw [Matrix.det_fin_two_of]
      apply mul_left_cancel₀ hlpos.ne'
      linear_combination hdet + δ 0 1 * hc1 + δ 0 1 * L * hm - ((j:ℕ):ℤ) * δ 0 0 * δ 0 1 * hLl - δ 0 0 * hd1
    let g : SL(2,ℤ) := ⟨M, hM⟩
    have hmem : g ∈ Gamma0 L := by
      rw [Gamma0_mem]; simp [g, M]
    refine ⟨(j, ⟨g, hmem⟩), trivial, ?_⟩
    ext r s
    fin_cases r <;> fin_cases s
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -(L:ℤ) * hm - hc1
    · simp [g, M, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -hd1 - ((j:ℕ):ℤ) * δ 0 1 * hLl

end GlobalTheory.EisM.RightRepU
