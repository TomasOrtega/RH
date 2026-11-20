import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.InvApi
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTSlashInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixActionMemHomogeneousPolyFunctionsStatement

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

/- English proof (translation)
Establish `hpl : ¬ p ∣ N * l`. Introduce `h`. Use `Nat.Coprime.coprime_dvd_right h (by rw [mul_comm]; exact hc)` as an intermediate fact. Conclude with `hp.one_lt.ne' ((Nat.coprime_self p).1 this)`. Establish `hpN : p.Coprime N` using `Nat.Coprime.coprime_dvd_right (dvd_mul_left N l) hc`.

Establish `hpNl : p.Coprime (N * l)` using `by rw [mul_comm]; exact hc`. Establish `hD` using `Betti.isDiam_sgD (N := N) (l := l) (d := p) hN.ne' hl.ne_zero hpN`. Establish `hD'` using `Betti.isDiam_sgD (N := N * l) (l := l) (d := p) (Nat.mul_ne_zero hN.ne' hl.ne_zero) hl.ne_zero hpNl`. Use `set σ := sgD N l p with hσ`. Use `set σ' := sgD (N * l) l p with hσ'`.

Establish `hdia : GlobalTheory.Hk.IsDia N l p σ'`. Use `⟨CongruenceSubgroup.Gamma0_mem.1 hD'.1.1, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) hD'.2`. Simplify `h2` using `[GlobalTheory.KZ.en]`. Establish `hδ : σ * σ'⁻¹ ∈ Gam N l`.

Use `⟨?_, Subgroup.mul_mem _ hD.1.2 (Subgroup.inv_mem _ hD'.1.2)⟩` and prove the remaining obligations. Establish `h0` using `CongruenceSubgroup.Gamma0_mem.1 hD.1.1`. Establish `h1` using `hD.2`. Establish `h0' : (((σ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0`. Use `congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) (CongruenceSubgroup.Gamma0_mem.1 hD'.1.1)` as an intermediate fact.

Simplify using `using this`. Establish `h1' : (((σ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = p`. Establish `h2` using `congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) hD'.2`. Simplify `h2` using `[GlobalTheory.KZ.en]`. Simplify using `only [GlobalTheory.KZ.en] at h1`.

Establish `hdet` using `σ.det_coe`. Establish `hdet'` using `σ'.det_coe`. Rewrite `hdet`, `hdet'` using `[Matrix.det_fin_two]`. Establish `e1` using `congrArg (Int.cast : ℤ → ZMod N) hdet`. Establish `e2` using `congrArg (Int.cast : ℤ → ZMod N) hdet'`.

Move the coercions through the operations in `at e1 e2`. Rewrite `e1` using `[h0, h1]`. Rewrite `e2` using `[h0', h1']`. Use `show σ * σ'⁻¹ ∈ CongruenceSubgroup.Gamma1 N`. Rewrite using `[CongruenceSubgroup.Gamma1_mem]`.

Simplify using `only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]`. Use `push_cast`. Rewrite using `[h0, h1, h0', h1']`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `all_goals first | linear_combination e1 | linear_combination e2 | ring`.

Take `⟨π, hπ⟩` from `GlobalTheory.HkInv.perm N l p σ' γ hp hpl hdia hγ`. Set `D : Fin (p + 1) → SL(2, ℤ)` to `fun i => if (i : ℕ) < p then 1 else σ * σ'⁻¹`. Establish `hDm : ∀ i, D i ∈ Gam N l`. Introduce `i`. Simplify using `only [D]`.

Use `split_ifs`. Conclude with `one_mem _`. Conclude with `hδ`. Establish `hT : ∀ i, GlobalTheory.HeckeFamilyMatrices.tqFam p σ i = (D i : Matrix (Fin 2) (Fin 2) ℤ) * GlobalTheory.HeckeFamilyMatrices.tqFam p σ' i`. Introduce `i`.

Simplify using `only [GlobalTheory.HeckeFamilyMatrices.tqFam, D]`. Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, ← Matrix.mul_assoc ((σ'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]`. Use `⟨π, fun i => ?_⟩` and prove the remaining obligations.

Take `⟨γ', hγ', he⟩` from `hπ i`. Use `⟨D i * γ' * (D (π i))⁻¹, mul_mem (mul_mem (hDm i) hγ') (inv_mem (hDm _)), ?_⟩` and prove the remaining obligations. Rewrite using `[hT i, hT (π i), Matrix.mul_assoc]`. Use `erw [he]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_assoc (D i * γ'), inv_mul_cancel, mul_one]`.
-/
private theorem hi_perm (N l p : ℕ) (hl : l.Prime) (hN : 0 < N) (hp : p.Prime) (hc : Nat.Coprime p (l * N))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) :
    ∃ π : Equiv.Perm (Fin (p + 1)), ∀ i, ∃ γ' ∈ Gam N l,
      GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        (γ' : Matrix (Fin 2) (Fin 2) ℤ) * GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i) := by
  have hpl : ¬ p ∣ N * l := by
    intro h
    have := Nat.Coprime.coprime_dvd_right h (by rw [mul_comm]; exact hc)
    exact hp.one_lt.ne' ((Nat.coprime_self p).1 this)
  have hpN : p.Coprime N := Nat.Coprime.coprime_dvd_right (dvd_mul_left N l) hc
  have hpNl : p.Coprime (N * l) := by rw [mul_comm]; exact hc
  have hD := Betti.isDiam_sgD (N := N) (l := l) (d := p) hN.ne' hl.ne_zero hpN
  have hD' := Betti.isDiam_sgD (N := N * l) (l := l) (d := p) (Nat.mul_ne_zero hN.ne' hl.ne_zero) hl.ne_zero hpNl
  set σ := sgD N l p with hσ
  set σ' := sgD (N * l) l p with hσ'
  have hdia : GlobalTheory.Hk.IsDia N l p σ' := by
    refine ⟨CongruenceSubgroup.Gamma0_mem.1 hD'.1.1, ?_⟩
    have h2 := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) hD'.2
    simpa [GlobalTheory.KZ.en] using h2
  have hδ : σ * σ'⁻¹ ∈ Gam N l := by
    refine ⟨?_, Subgroup.mul_mem _ hD.1.2 (Subgroup.inv_mem _ hD'.1.2)⟩
    have h0 := CongruenceSubgroup.Gamma0_mem.1 hD.1.1
    have h1 := hD.2
    have h0' : (((σ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 := by
      have := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) (CongruenceSubgroup.Gamma0_mem.1 hD'.1.1)
      simpa using this
    have h1' : (((σ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = p := by
      have h2 := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) hD'.2
      simpa [GlobalTheory.KZ.en] using h2
    simp only [GlobalTheory.KZ.en] at h1
    have hdet := σ.det_coe
    have hdet' := σ'.det_coe
    rw [Matrix.det_fin_two] at hdet hdet'
    have e1 := congrArg (Int.cast : ℤ → ZMod N) hdet
    have e2 := congrArg (Int.cast : ℤ → ZMod N) hdet'
    push_cast at e1 e2
    rw [h0, h1] at e1
    rw [h0', h1'] at e2
    show σ * σ'⁻¹ ∈ CongruenceSubgroup.Gamma1 N
    rw [CongruenceSubgroup.Gamma1_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    push_cast
    rw [h0, h1, h0', h1']
    refine ⟨?_, ?_, ?_⟩
    all_goals first | linear_combination e1 | linear_combination e2 | ring
  obtain ⟨π, hπ⟩ := GlobalTheory.HkInv.perm N l p σ' γ hp hpl hdia hγ
  let D : Fin (p + 1) → SL(2, ℤ) := fun i => if (i : ℕ) < p then 1 else σ * σ'⁻¹
  have hDm : ∀ i, D i ∈ Gam N l := by
    intro i
    simp only [D]
    split_ifs
    · exact one_mem _
    · exact hδ
  have hT : ∀ i, GlobalTheory.HeckeFamilyMatrices.tqFam p σ i = (D i : Matrix (Fin 2) (Fin 2) ℤ) * GlobalTheory.HeckeFamilyMatrices.tqFam p σ' i := by
    intro i
    simp only [GlobalTheory.HeckeFamilyMatrices.tqFam, D]
    split_ifs
    · simp
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, ← Matrix.mul_assoc ((σ'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ),
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  refine ⟨π, fun i => ?_⟩
  obtain ⟨γ', hγ', he⟩ := hπ i
  refine ⟨D i * γ' * (D (π i))⁻¹, mul_mem (mul_mem (hDm i) hγ') (inv_mem (hDm _)), ?_⟩
  rw [hT i, hT (π i), Matrix.mul_assoc]
  erw [he]
  rw [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_assoc (D i * γ'), inv_mul_cancel, mul_one]

/- English proof (translation)
Unfold `GlobalTheory.HeckeFamilyMatrices.tqFam`. Use `split_ifs`. Simplify using `[Matrix.det_fin_two]`. Conclude with `hp` after adjusting the coercions. Rewrite using `[Matrix.det_mul, GlobalTheory.HeckeFamilyMatrices.mat, σ.det_coe, one_mul]`.

Simplify using `[GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two]`. Conclude with `hp` after adjusting the coercions.
-/
private theorem hi_det (p : ℕ) (hp : 0 < p) (σ : SL(2, ℤ)) (i : Fin (p + 1)) : 0 < (GlobalTheory.HeckeFamilyMatrices.tqFam p σ i).det := by
  unfold GlobalTheory.HeckeFamilyMatrices.tqFam
  split_ifs
  · simp [Matrix.det_fin_two]
    exact_mod_cast hp
  · rw [Matrix.det_mul, GlobalTheory.HeckeFamilyMatrices.mat, σ.det_coe, one_mul]
    simp [GlobalTheory.HeckeFamilyMatrices.dg, Matrix.det_fin_two]
    exact_mod_cast hp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [GlobalTheory.KZ.Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply]`. Use `congr 1`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun j => (X.act l !![1, (j : ℤ); 0, (p : ℤ)]) a)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `[GlobalTheory.HeckeFamilyMatrices.tqFam]`. Simplify using `[GlobalTheory.HeckeFamilyMatrices.tqFam, GlobalTheory.HeckeFamilyMatrices.dg]`.
-/
private theorem hi_sum (N p : ℕ) (a : X.Fn l) :
    X.heckeT N l p a = ∑ i : Fin (p + 1), X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) a := by
  rw [Fin.sum_univ_castSucc]
  simp only [GlobalTheory.KZ.Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun j => (X.act l !![1, (j : ℤ); 0, (p : ℤ)]) a)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [GlobalTheory.HeckeFamilyMatrices.tqFam]
  · simp [GlobalTheory.HeckeFamilyMatrices.tqFam, GlobalTheory.HeckeFamilyMatrices.dg]

/- English proof (translation)
Take `⟨π, hπ⟩` from `hi_perm N l p (Fact.out) hN hp hc γ hγ`. Use `choose g hg he using hπ`. Use `⟨π, g, hg, fun a => ?_⟩` and prove the remaining obligations. Establish `hd1 : ∀ δ : SL(2, ℤ), 0 < (δ : Matrix (Fin 2) (Fin 2) ℤ).det` using `fun δ => by rw [δ.det_coe]; exact one_pos`. Rewrite using `[hi_sum X l N p a, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.KZ.Tower.act_act Ω ε X l _ _ (hi_det p hp.pos _ i) (hd1 γ), GlobalTheory.KZ.Tower.act_act Ω ε X l _ _ (hd1 (g i)) (hi_det p hp.pos _ (π i)), he i]`.
-/
private theorem hi_act (N p : ℕ) (hN : 0 < N) (hp : p.Prime) (hc : Nat.Coprime p (l * N))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) :
    ∃ (π : Equiv.Perm (Fin (p + 1))) (g : Fin (p + 1) → SL(2, ℤ)), (∀ i, g i ∈ Gam N l) ∧ ∀ a : X.Fn l,
      X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeT N l p a) =
        ∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i)) (X.act l (g i : Matrix (Fin 2) (Fin 2) ℤ) a) := by
  obtain ⟨π, hπ⟩ := hi_perm N l p (Fact.out) hN hp hc γ hγ
  choose g hg he using hπ
  refine ⟨π, g, hg, fun a => ?_⟩
  have hd1 : ∀ δ : SL(2, ℤ), 0 < (δ : Matrix (Fin 2) (Fin 2) ℤ).det := fun δ => by rw [δ.det_coe]; exact one_pos
  rw [hi_sum X l N p a, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.KZ.Tower.act_act Ω ε X l _ _ (hi_det p hp.pos _ i) (hd1 γ), GlobalTheory.KZ.Tower.act_act Ω ε X l _ _ (hd1 (g i)) (hi_det p hp.pos _ (π i)), he i]

/- English proof (translation)
Use `choose c hcA hcu using h`. Use `⟨fun k => ∑ i ∈ S, c i k, fun k => Submodule.sum_mem _ fun i _ => hcA i k, fun u => ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.sum_apply, hcu, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`.
-/
private theorem hi_pol_sum (w : ℕ) {ι : Type} (S : Finset ι) (t : ι → X.Fn l) (h : ∀ i, t i ∈ X.Pol l w) :
    ∑ i ∈ S, t i ∈ X.Pol l w := by
  choose c hcA hcu using h
  refine ⟨fun k => ∑ i ∈ S, c i k, fun k => Submodule.sum_mem _ fun i _ => hcA i k, fun u => ?_⟩
  simp only [Finset.sum_apply, hcu, Finset.smul_sum]
  rw [Finset.sum_comm]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Use `⟨1, fun W _ => ⟨1, by simp⟩, ?_⟩` and prove the remaining obligations. Simplify using `[UpperTheory.Kd.K4.Rep, GlobalTheory.KZ.Tower.cls]`. Consider the case `insert i S hi ih`.

Take `⟨f, hf, hr⟩` from `ih`. Take `⟨f', hf', hr'⟩` from `h i`. Use `⟨f' * f, fun W hW => ?_, ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `hf W hW`. Take `⟨g', hg'⟩` from `hf' W hW`.

Use `⟨g' * g, ?_⟩` and prove the remaining obligations. Establish `: ((f' * f : X.Kˣ) : X.K) / ((g' * g : X.Kˣ) : X.K) ^ (l ^ n) = ((f' : X.K) / (g' : X.K) ^ (l ^ n)) * ((f : X.K) / (g : X.K) ^ (l ^ n))`. Rewrite using `[Units.val_mul, Units.val_mul, mul_pow, div_mul_div_comm]`. Rewrite using `[this, map_mul, hg, hg', one_mul]`. Unfold `UpperTheory.Kd.K4.Rep at *`.

Rewrite using `[Finset.sum_insert hi, map_add, hr, hr']`. Simplify using `only [GlobalTheory.KZ.Tower.cls, ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]`.
-/
private theorem hi_rep_sum (n : ℕ) {ι : Type} (S : Finset ι) (c : ι → X.Khat l)
    (h : ∀ i, ∃ f ∈ X.Un (l ^ n), UpperTheory.Kd.K4.Rep X l n f (c i)) : ∃ f ∈ X.Un (l ^ n), UpperTheory.Kd.K4.Rep X l n f (∑ i ∈ S, c i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, fun W _ => ⟨1, by simp⟩, ?_⟩
    simp [UpperTheory.Kd.K4.Rep, GlobalTheory.KZ.Tower.cls]
  | insert i S hi ih =>
    obtain ⟨f, hf, hr⟩ := ih
    obtain ⟨f', hf', hr'⟩ := h i
    refine ⟨f' * f, fun W hW => ?_, ?_⟩
    · obtain ⟨g, hg⟩ := hf W hW
      obtain ⟨g', hg'⟩ := hf' W hW
      refine ⟨g' * g, ?_⟩
      have : ((f' * f : X.Kˣ) : X.K) / ((g' * g : X.Kˣ) : X.K) ^ (l ^ n) = ((f' : X.K) / (g' : X.K) ^ (l ^ n)) * ((f : X.K) / (g : X.K) ^ (l ^ n)) := by
        rw [Units.val_mul, Units.val_mul, mul_pow, div_mul_div_comm]
      rw [this, map_mul, hg, hg', one_mul]
    · unfold UpperTheory.Kd.K4.Rep at *
      rw [Finset.sum_insert hi, map_add, hr, hr']
      simp only [GlobalTheory.KZ.Tower.cls, ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]

/- English proof (translation)
Use `choose c hc hcu using h`. Use `⟨fun k => ∑ i ∈ S, c i k, fun k => hi_rep_sum X l n S (fun i => c i k) (fun i => hc i k), fun u => ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.sum_apply, hcu, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`.
-/
private theorem hi_polMod_sum (w n : ℕ) {ι : Type} (S : Finset ι) (t : ι → X.Fn l) (h : ∀ i, PolMod X l w n (t i)) :
    PolMod X l w n (∑ i ∈ S, t i) := by
  choose c hc hcu using h
  refine ⟨fun k => ∑ i ∈ S, c i k, fun k => hi_rep_sum X l n S (fun i => c i k) (fun i => hc i k), fun u => ?_⟩
  simp only [Finset.sum_apply, hcu, Finset.smul_sum]
  rw [Finset.sum_comm]

/- English proof (translation)
Establish `hA` using `(GlobalTheory.KZ.kmap_A_stable ε X ε.injective (by obtain ⟨φ, h1, h2⟩ := X.j_hol; exact ⟨φ, h2, h1⟩) l).1`. Establish `key : ∀ x ∈ X.BSet N l w, X.heckeT N l p x ∈ X.BSet N l w`. Introduce and unpack `x ⟨hxP, hxI⟩`. Use `⟨?_, fun γ hγ => ?_⟩` and prove the remaining obligations. Rewrite using `[hi_sum X l N p x]`.

Conclude with `hi_pol_sum X l w Finset.univ _ (fun i => GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions X l w _ (fun a ha => hA _ a ha) x hxP)`. Take `⟨π, g, hg, he⟩` from `hi_act X l N p hN hp hc γ hγ`. Rewrite using `[he x, hi_sum X l N p x]`. Combine the equalities or inequalities in the displayed calculation. Establish `hle : X.B N l w ≤ (X.B N l w).comap (X.heckeT N l p)` using `Submodule.span_le.2 (fun x hx => Submodule.subset_span (key x hx))`.

Conclude with `hle hb`.
-/
private theorem hi_B [IsAlgClosure ℚ Ω] (N w p : ℕ) (hN : 0 < N) (hp : p.Prime) (hc : Nat.Coprime p (l * N))
    (b : X.Fn l) (hb : b ∈ X.B N l w) : X.heckeT N l p b ∈ X.B N l w := by
  have hA := (GlobalTheory.KZ.kmap_A_stable ε X ε.injective (by obtain ⟨φ, h1, h2⟩ := X.j_hol; exact ⟨φ, h2, h1⟩) l).1
  have key : ∀ x ∈ X.BSet N l w, X.heckeT N l p x ∈ X.BSet N l w := by
    rintro x ⟨hxP, hxI⟩
    refine ⟨?_, fun γ hγ => ?_⟩
    · rw [hi_sum X l N p x]
      exact hi_pol_sum X l w Finset.univ _ (fun i => GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions X l w _ (fun a ha => hA _ a ha) x hxP)
    · obtain ⟨π, g, hg, he⟩ := hi_act X l N p hN hp hc γ hγ
      rw [he x, hi_sum X l N p x]
      calc _ = ∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i)) x :=
            Finset.sum_congr rfl fun i _ => by rw [hxI _ (hg i)]
        _ = _ := Equiv.sum_comp π (fun i => X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) x)
  have hle : X.B N l w ≤ (X.B N l w).comap (X.heckeT N l p) :=
    Submodule.span_le.2 (fun x hx => Submodule.subset_span (key x hx))
  exact hle hb

end UpperTheory.V.Z.Kato.Nb

/- English proof (translation)
Introduce `Ω _ _ _ ε X l _ N w n p hN hp hc a ha`. Take `⟨⟨t, hPt, hCt⟩, hinv, b, hbB, hbL⟩` from `ha`. Take `⟨hEq, -, -, hSum, -, hAct, -⟩` from `sApi Ω ε X l n`. Establish `hPolAct` using `(sInvApi Ω ε X l N w n).2.2.2.2.2.2.2`. Establish `hH : ∀ x y, CgF X l n x y → CgF X l n (X.heckeT N l p x) (X.heckeT N l p y)`.

Introduce `x y hxy`. Rewrite using `[hi_sum X l N p x, hi_sum X l N p y]`. Conclude with `hSum _ Finset.univ _ _ (fun i _ => hAct _ _ _ hxy)`. Use `⟨⟨∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) t, ?_, ?_⟩, fun γ hγ => ?_, X.heckeT N l p b, hi_B X l N w p hN hp hc b hbB, fun u => ?_⟩` and prove the remaining obligations. Conclude with `hi_polMod_sum X l w n Finset.univ _ (fun i => hPolAct _ t (hi_det p hp.pos _ i) hPt)`.

Rewrite using `[hi_sum X l N p a]`. Conclude with `hSum _ Finset.univ _ _ (fun i _ => hAct _ _ _ hCt)`. Take `⟨π, g, hg, he⟩` from `hi_act X l N p hN hp hc γ hγ`. Rewrite using `[he a]`. Establish `h2 : X.heckeT N l p a = ∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i)) a`.

Rewrite using `[hi_sum X l N p a]`. Conclude with `(Equiv.sum_comp π (fun i => X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) a)).symm`. Rewrite using `[h2]`. Conclude with `hSum _ Finset.univ _ _ (fun i _ => hAct _ _ _ (hinv (g i) (hg i)))`. Establish `hba : CgF X l n b ((l : ℤ_[l]) ^ cL X l N w • a)` using `fun u => by simpa using hbL u`.

Use `hH _ _ hba u` as an intermediate fact. Simplify `this` using `[map_smul]`.
-/
theorem UpperTheory.V.Z.Kato.Nb.sHeckeInv :
    UpperTheory.V.Z.Kato.Nb.SHeckeInv := by
  intro Ω _ _ _ ε X l _ N w n p hN hp hc a ha
  obtain ⟨⟨t, hPt, hCt⟩, hinv, b, hbB, hbL⟩ := ha
  obtain ⟨hEq, -, -, hSum, -, hAct, -⟩ := sApi Ω ε X l n
  have hPolAct := (sInvApi Ω ε X l N w n).2.2.2.2.2.2.2
  have hH : ∀ x y, CgF X l n x y → CgF X l n (X.heckeT N l p x) (X.heckeT N l p y) := by
    intro x y hxy
    rw [hi_sum X l N p x, hi_sum X l N p y]
    exact hSum _ Finset.univ _ _ (fun i _ => hAct _ _ _ hxy)
  refine ⟨⟨∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) t, ?_, ?_⟩, fun γ hγ => ?_, X.heckeT N l p b, hi_B X l N w p hN hp hc b hbB, fun u => ?_⟩
  · exact hi_polMod_sum X l w n Finset.univ _ (fun i => hPolAct _ t (hi_det p hp.pos _ i) hPt)
  · rw [hi_sum X l N p a]
    exact hSum _ Finset.univ _ _ (fun i _ => hAct _ _ _ hCt)
  · obtain ⟨π, g, hg, he⟩ := hi_act X l N p hN hp hc γ hγ
    rw [he a]
    have h2 : X.heckeT N l p a = ∑ i, X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) (π i)) a := by
      rw [hi_sum X l N p a]
      exact (Equiv.sum_comp π (fun i => X.act l (GlobalTheory.HeckeFamilyMatrices.tqFam p (sgD N l p) i) a)).symm
    rw [h2]
    exact hSum _ Finset.univ _ _ (fun i _ => hAct _ _ _ (hinv (g i) (hg i)))
  · have hba : CgF X l n b ((l : ℤ_[l]) ^ cL X l N w • a) := fun u => by simpa using hbL u
    have := hH _ _ hba u
    simpa [map_smul] using this
