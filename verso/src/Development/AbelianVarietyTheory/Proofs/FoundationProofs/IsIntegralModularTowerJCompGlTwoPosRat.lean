import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariantStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.JInt

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

/- English proof (translation)
Establish `h` using `g.2`. Rewrite `h` using `[Matrix.mem_glpos]`. Simplify `h` using `[ent, Matrix.det_fin_two]`.
-/
lemma det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := g.2
  rw [Matrix.mem_glpos] at h
  simpa [ent, Matrix.det_fin_two] using h

/- English proof (translation)
Introduce `h`. Establish `him` using `congrArg Complex.im h`. Establish `hre` using `congrArg Complex.re h`. Establish `hz' : 0 < z.im` using `hz`. Simplify using `at him hre`.

Establish `hc : ent g 1 0 = 0`. Break down `him with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd h1 hz'.ne'`. Rewrite `hre` using `[hc]`.

Simplify using `at hre`. Use `det_pos g` as an intermediate fact. Rewrite `this` using `[hc, hre]`. Simplify using `at this`.
-/
lemma den_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  have hz' : 0 < z.im := hz
  simp at him hre
  have hc : ent g 1 0 = 0 := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 hz'.ne'
  rw [hc] at hre
  simp at hre
  have := det_pos g
  rw [hc, hre] at this
  simp at this

/- English proof (translation)
Establish `hd` using `den_ne g hz`. Establish `hz' : 0 < z.im` using `hz`. Establish `hn : 0 < Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))` using `Complex.normSq_pos.2 hd`. Establish `key : (mob g z).im = ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) * z.im / Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))`. Simplify using `only [mob]`.

Rewrite using `[Complex.div_im]`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `show 0 < (mob g z).im`.

Rewrite using `[key]`. Use `det_pos g` as an intermediate fact. Establish `: (0 : ℝ) < ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ)` using `by exact_mod_cast this`. Check the signs of the components of the expression.
-/
lemma mob_im (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  have hd := den_ne g hz
  have hz' : 0 < z.im := hz
  have hn : 0 < Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := Complex.normSq_pos.2 hd
  have key : (mob g z).im = ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) * z.im /
      Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := by
    simp only [mob]
    rw [Complex.div_im]
    simp
    field_simp
    ring
  show 0 < (mob g z).im
  rw [key]
  have := det_pos g
  have : (0 : ℝ) < ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) := by exact_mod_cast this
  positivity

/- English proof (translation)
Introduce `z hz`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Use `show DifferentiableAt ℂ (fun z => ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) / ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))) z`. Conclude with `((differentiableAt_id.const_mul _).add_const _).div ((differentiableAt_id.const_mul _).add_const _) (den_ne g hz)`.
-/
lemma mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun z => ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) / ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))) z
  exact ((differentiableAt_id.const_mul _).add_const _).div
    ((differentiableAt_id.const_mul _).add_const _) (den_ne g hz)

def holR (X : Tower Ω ε) : Subring X.K where
  carrier := {h | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)}
  mul_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    exact ⟨φ * ψ, hφ.mul hψ, by rw [map_mul, ha, hb]; rfl⟩
  one_mem' := ⟨fun _ => 1, differentiableOn_const 1, by rw [map_one]; rfl⟩
  add_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    exact ⟨φ + ψ, hφ.add hψ, by rw [map_add, ha, hb]; rfl⟩
  zero_mem' := ⟨fun _ => 0, differentiableOn_const 0, by rw [map_zero]; rfl⟩
  neg_mem' := by
    rintro a ⟨φ, hφ, ha⟩
    exact ⟨-φ, hφ.neg, by rw [map_neg, ha]; rfl⟩

end GlobalTheory.KZ.JInt

namespace GlobalTheory.KZ.JInt

open Polynomial in

/- English proof (translation)
Introduce `Ω _ _ _ ε Tw hε hj g`. Use `set f := Tw.sl g Tw.jK with hf`. Take `⟨M, hM, hlev⟩` from `Tw.level f`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Set `red : SL(2, ℤ) →* SL(2, ZMod M)` to `Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))`.

Establish `hred : ∀ γ γ' : SL(2, ℤ), red γ = red γ' → Tw.sl (ofSL γ) f = Tw.sl (ofSL γ') f`. Introduce `γ γ' h`. Establish `hmem : γ' * γ⁻¹ ∈ CongruenceSubgroup.Gamma M`. Rewrite using `[CongruenceSubgroup.Gamma_mem']`. Use `show red (γ' * γ⁻¹) = 1`.

Rewrite using `[map_mul, map_inv, h, mul_inv_cancel]`. Establish `e : γ' = (γ' * γ⁻¹) * γ` using `by group`. Rewrite using `[e, map_mul, Tw.sl_mul, hlev _ hmem]`. Set `S : Set Tw.K` to `Set.range fun γ : SL(2, ℤ) => Tw.sl (ofSL γ) f`. Establish `hSfin : S.Finite` using `by classical`.

Set `F : SL(2, ZMod M) → Tw.K` to `fun γb => if h : ∃ γ, red γ = γb then Tw.sl (ofSL h.choose) f else 0`. Apply `(Set.finite_range F).subset` to reduce the goal to its premises. Introduce and unpack `_ ⟨γ, rfl⟩`. Use `⟨red γ, ?_⟩` and prove the remaining obligations. Establish `h : ∃ γ', red γ' = red γ` using `⟨γ, rfl⟩`.

Simplify using `only [F, dif_pos h]`. Conclude with `hred _ _ h.choose_spec`. Set `T` to `hSfin.toFinset`. Establish `hT : ∀ y, y ∈ T ↔ y ∈ S` using `fun y => Set.Finite.mem_toFinset hSfin`. Set `P : Tw.K[X]` to `∏ y ∈ T, (X - C y)`.

Establish `hPmon : P.Monic` using `monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y`. Establish `hfT : f ∈ T`. Rewrite using `[hT]; exact ⟨1, by simp [Tw.sl_one]⟩`. Establish `hPf : P.eval f = 0`. Rewrite using `[eval_prod]`.

Conclude with `Finset.prod_eq_zero hfT (by simp)`. Establish `hinv : ∀ (δ : SL(2, ℤ)) (n : ℕ), Tw.sl (ofSL δ) (P.coeff n) = P.coeff n`. Introduce `δ n`. Establish `hmap : P.map ((Tw.sl (ofSL δ) : Tw.K ≃ₐ[Ω] Tw.K) : Tw.K →+* Tw.K) = P`. Simplify using `only [P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]`.

Use `Finset.prod_nbij' (fun y => Tw.sl (ofSL δ) y) (fun y => Tw.sl (ofSL δ⁻¹) y) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy`, the goal using `[hT]`. Take `⟨γ, rfl⟩` from `hy`. Conclude with `⟨γ * δ, by simp only [map_mul, Tw.sl_mul]⟩`.

Introduce `y hy`. Rewrite `hy`, the goal using `[hT]`. Take `⟨γ, rfl⟩` from `hy`. Conclude with `⟨γ * δ⁻¹, by simp only [map_mul, Tw.sl_mul]⟩`. Introduce `y _`.

Rewrite using `[← Tw.sl_mul, ← map_mul, mul_inv_cancel, map_one, Tw.sl_one]`. Introduce `y _`. Rewrite using `[← Tw.sl_mul, ← map_mul, inv_mul_cancel, map_one, Tw.sl_one]`. Introduce `y _`. Both sides reduce to the same expression.

Use `congrArg (fun p => p.coeff n) hmap` as an intermediate fact. Simplify `this` using `[coeff_map]`. Take `⟨φ, hφ, hjφ⟩` from `hj`. Establish `hmemS : ∀ y ∈ T, y ∈ holR Tw`. Introduce `y hy`.

Rewrite `hy` using `[hT]`. Take `⟨γ, rfl⟩` from `hy`. Establish `e : Tw.sl (ofSL γ) f = Tw.sl (g * ofSL γ) Tw.jK` using `by rw [Tw.sl_mul]`. Use `show Tw.sl (ofSL γ) f ∈ holR Tw`. Rewrite using `[e]`.

Conclude with `⟨fun z => φ (mob (g * ofSL γ) z), hφ.comp (mob_diff _) (fun z hz => mob_im _ hz), Tw.an_sl _ _ _ hjφ⟩`. Set `Q : (holR Tw)[X]` to `∏ y ∈ T.attach, (X - C ⟨y.1, hmemS y.1 y.2⟩)`. Establish `hQ : Q.map (holR Tw).subtype = P`. Simplify using `only [Q, P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, Subring.subtype_apply]`. Conclude with `Finset.prod_attach T (fun y => X - C y)`.

Establish `hhol : ∀ n, P.coeff n ∈ holR Tw`. Introduce `n`. Rewrite using `[← hQ, coeff_map]`. Conclude with `(Q.coeff n).2`. Establish `hA : ∀ n, P.coeff n ∈ Algebra.adjoin Ω {Tw.jK}` using `fun n => GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε Tw hε ⟨φ, hφ, hjφ⟩ (P.coeff n) (fun δ => hinv δ n) (hhol n)`.

Establish `hlift : P ∈ lifts (algebraMap (Algebra.adjoin Ω {Tw.jK}) Tw.K)`. Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `n`. Conclude with `⟨⟨_, hA n⟩, rfl⟩`. Take `⟨q, hqmap, -, hqmon⟩` from `lifts_and_natDegree_eq_and_monic hlift hPmon`.

Conclude with `⟨q, hqmon, by rw [eval₂_eq_eval_map, hqmap, hPf]⟩`.
-/
theorem jK_sl_isIntegral : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ g : GQ, IsIntegral (Algebra.adjoin Ω {X.jK}) (X.sl g X.jK) := by
  intro Ω _ _ _ ε Tw hε hj g
  set f := Tw.sl g Tw.jK with hf
  obtain ⟨M, hM, hlev⟩ := Tw.level f
  haveI : NeZero M := ⟨hM.ne'⟩
  let red : SL(2, ℤ) →* SL(2, ZMod M) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))

  have hred : ∀ γ γ' : SL(2, ℤ), red γ = red γ' → Tw.sl (ofSL γ) f = Tw.sl (ofSL γ') f := by
    intro γ γ' h
    have hmem : γ' * γ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
      rw [CongruenceSubgroup.Gamma_mem']
      show red (γ' * γ⁻¹) = 1
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have e : γ' = (γ' * γ⁻¹) * γ := by group
    rw [e, map_mul, Tw.sl_mul, hlev _ hmem]
  let S : Set Tw.K := Set.range fun γ : SL(2, ℤ) => Tw.sl (ofSL γ) f
  have hSfin : S.Finite := by
    classical
    let F : SL(2, ZMod M) → Tw.K := fun γb => if h : ∃ γ, red γ = γb then Tw.sl (ofSL h.choose) f else 0
    apply (Set.finite_range F).subset
    rintro _ ⟨γ, rfl⟩
    refine ⟨red γ, ?_⟩
    have h : ∃ γ', red γ' = red γ := ⟨γ, rfl⟩
    simp only [F, dif_pos h]
    exact hred _ _ h.choose_spec
  let T := hSfin.toFinset
  have hT : ∀ y, y ∈ T ↔ y ∈ S := fun y => Set.Finite.mem_toFinset hSfin
  let P : Tw.K[X] := ∏ y ∈ T, (X - C y)
  have hPmon : P.Monic := monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hfT : f ∈ T := by
    rw [hT]; exact ⟨1, by simp [Tw.sl_one]⟩
  have hPf : P.eval f = 0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero hfT (by simp)

  have hinv : ∀ (δ : SL(2, ℤ)) (n : ℕ), Tw.sl (ofSL δ) (P.coeff n) = P.coeff n := by
    intro δ n
    have hmap : P.map ((Tw.sl (ofSL δ) : Tw.K ≃ₐ[Ω] Tw.K) : Tw.K →+* Tw.K) = P := by
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
      refine Finset.prod_nbij' (fun y => Tw.sl (ofSL δ) y) (fun y => Tw.sl (ofSL δ⁻¹) y) ?_ ?_ ?_ ?_ ?_
      · intro y hy
        rw [hT] at hy ⊢
        obtain ⟨γ, rfl⟩ := hy
        exact ⟨γ * δ, by simp only [map_mul, Tw.sl_mul]⟩
      · intro y hy
        rw [hT] at hy ⊢
        obtain ⟨γ, rfl⟩ := hy
        exact ⟨γ * δ⁻¹, by simp only [map_mul, Tw.sl_mul]⟩
      · intro y _
        rw [← Tw.sl_mul, ← map_mul, mul_inv_cancel, map_one, Tw.sl_one]
      · intro y _
        rw [← Tw.sl_mul, ← map_mul, inv_mul_cancel, map_one, Tw.sl_one]
      · intro y _
        rfl
    have := congrArg (fun p => p.coeff n) hmap
    simpa [coeff_map] using this

  obtain ⟨φ, hφ, hjφ⟩ := hj
  have hmemS : ∀ y ∈ T, y ∈ holR Tw := by
    intro y hy
    rw [hT] at hy
    obtain ⟨γ, rfl⟩ := hy
    have e : Tw.sl (ofSL γ) f = Tw.sl (g * ofSL γ) Tw.jK := by rw [Tw.sl_mul]
    show Tw.sl (ofSL γ) f ∈ holR Tw
    rw [e]
    exact ⟨fun z => φ (mob (g * ofSL γ) z),
      hφ.comp (mob_diff _) (fun z hz => mob_im _ hz), Tw.an_sl _ _ _ hjφ⟩
  let Q : (holR Tw)[X] := ∏ y ∈ T.attach, (X - C ⟨y.1, hmemS y.1 y.2⟩)
  have hQ : Q.map (holR Tw).subtype = P := by
    simp only [Q, P, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C, Subring.subtype_apply]
    exact Finset.prod_attach T (fun y => X - C y)
  have hhol : ∀ n, P.coeff n ∈ holR Tw := by
    intro n
    rw [← hQ, coeff_map]
    exact (Q.coeff n).2

  have hA : ∀ n, P.coeff n ∈ Algebra.adjoin Ω {Tw.jK} := fun n =>
    GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant ε Tw hε ⟨φ, hφ, hjφ⟩ (P.coeff n) (fun δ => hinv δ n) (hhol n)
  have hlift : P ∈ lifts (algebraMap (Algebra.adjoin Ω {Tw.jK}) Tw.K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hA n⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqmon⟩ := lifts_and_natDegree_eq_and_monic hlift hPmon
  exact ⟨q, hqmon, by rw [eval₂_eq_eval_map, hqmap, hPf]⟩

end GlobalTheory.KZ.JInt
