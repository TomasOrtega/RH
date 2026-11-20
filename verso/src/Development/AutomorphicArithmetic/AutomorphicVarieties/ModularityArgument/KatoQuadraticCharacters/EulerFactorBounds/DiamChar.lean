import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.DiamEx
import Development.AbelianVarietyTheory.Definitions.Foundations.OpLDOneSubMemTriv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

namespace UpperTheory.V.Z.Kato.Nb

open CongruenceSubgroup

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Unfold `Tower.B at hb`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem x hx => exact hx.2 γ hγ`. Consider the case `zero => exact map_zero _`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`.

Consider the case `smul a x _ hx => rw [map_smul, hx]`.
-/
private theorem dc_fix (N w : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  unfold Tower.B at hb
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

/- English proof (translation)
Rewrite using `[Tower.act_act Ω ε X l _ _ (by rw [σ.2]; norm_num) (by rw [τ.2]; norm_num), Matrix.SpecialLinearGroup.coe_mul]`.
-/
private theorem dc_mul (σ τ : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (τ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
  rw [Tower.act_act Ω ε X l _ _ (by rw [σ.2]; norm_num) (by rw [τ.2]; norm_num),
    Matrix.SpecialLinearGroup.coe_mul]

/- English proof (translation)
Establish `h0` using `Gamma0_mem.1 hσ`. Simplify using `only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]`. Use `push_cast`. Rewrite using `[h0]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem dc_en (N : ℕ) (σ τ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (hτ : τ ∈ Gamma0 N) :
    (en (σ * τ) 1 1 : ZMod N) = (en σ 1 1 : ZMod N) * (en τ 1 1 : ZMod N) := by
  have h0 := Gamma0_mem.1 hσ
  simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [h0]
  ring

/- English proof (translation)
Take `⟨ρ, hρ⟩ : ∃ ρ, ρ = τ * σ⁻¹` from `⟨_, rfl⟩`. Establish `hτ' : τ = ρ * σ` using `by rw [hρ, inv_mul_cancel_right]`. Establish `hρ0 : ρ ∈ Gamma0 N ⊓ Gamma0 l`. Rewrite using `[hρ]`. Conclude with `Subgroup.mul_mem _ hτ (Subgroup.inv_mem _ hσ)`.

Establish `det1 : ∀ B : SL(2, ℤ), B ∈ Gamma0 N → (en B 0 0 : ZMod N) * (en B 1 1 : ZMod N) = 1`. Introduce `B hB`. Establish `h0` using `Gamma0_mem.1 hB`. Establish `hd` using `congrArg (fun z : ℤ => (z : ZMod N)) B.2`. Simplify using `only [Matrix.det_fin_two] at hd`.

Move the coercions through the operations in `at hd`. Rewrite `hd` using `[h0, mul_zero, sub_zero]`. Conclude with `hd`. Establish `hσ11 : (en σ⁻¹ 1 1 : ZMod N) = (en σ 0 0 : ZMod N)`. Simplify using `[en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]`.

Establish `hρ11 : (en ρ 1 1 : ZMod N) = 1`. Rewrite using `[hρ, dc_en N τ σ⁻¹ hτ.1 (Subgroup.inv_mem _ hσ.1), ← h, hσ11, mul_comm]`. Conclude with `det1 σ hσ.1`. Establish `hρ00 : (en ρ 0 0 : ZMod N) = 1`. Use `det1 ρ hρ0.1` as an intermediate fact.

Rewrite `this` using `[hρ11, mul_one]`. Conclude with `this`. Establish `hρG : ρ ∈ Gam N l` using `⟨(Gamma1_mem _ _).2 ⟨hρ00, hρ11, Gamma0_mem.1 hρ0.1⟩, hρ0.2⟩`. Rewrite using `[hτ', ← dc_mul X l ρ σ b, dc_fix X l N w ρ hρG b hb]`.
-/
private theorem dc_same (N w : ℕ) (σ τ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N ⊓ Gamma0 l) (hτ : τ ∈ Gamma0 N ⊓ Gamma0 l)
    (h : (en σ 1 1 : ZMod N) = (en τ 1 1 : ZMod N)) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (τ : Matrix (Fin 2) (Fin 2) ℤ) b := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = τ * σ⁻¹ := ⟨_, rfl⟩
  have hτ' : τ = ρ * σ := by rw [hρ, inv_mul_cancel_right]
  have hρ0 : ρ ∈ Gamma0 N ⊓ Gamma0 l := by
    rw [hρ]
    exact Subgroup.mul_mem _ hτ (Subgroup.inv_mem _ hσ)
  have det1 : ∀ B : SL(2, ℤ), B ∈ Gamma0 N → (en B 0 0 : ZMod N) * (en B 1 1 : ZMod N) = 1 := by
    intro B hB
    have h0 := Gamma0_mem.1 hB
    have hd := congrArg (fun z : ℤ => (z : ZMod N)) B.2
    simp only [Matrix.det_fin_two] at hd
    push_cast at hd
    rw [h0, mul_zero, sub_zero] at hd
    exact hd
  have hσ11 : (en σ⁻¹ 1 1 : ZMod N) = (en σ 0 0 : ZMod N) := by
    simp [en, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hρ11 : (en ρ 1 1 : ZMod N) = 1 := by
    rw [hρ, dc_en N τ σ⁻¹ hτ.1 (Subgroup.inv_mem _ hσ.1), ← h, hσ11, mul_comm]
    exact det1 σ hσ.1
  have hρ00 : (en ρ 0 0 : ZMod N) = 1 := by
    have := det1 ρ hρ0.1
    rw [hρ11, mul_one] at this
    exact this
  have hρG : ρ ∈ Gam N l := ⟨(Gamma1_mem _ _).2 ⟨hρ00, hρ11, Gamma0_mem.1 hρ0.1⟩, hρ0.2⟩
  rw [hτ', ← dc_mul X l ρ σ b, dc_fix X l N w ρ hρG b hb]

end UpperTheory.V.Z.Kato.Nb

/- English proof (translation)
Unfold `SDiamChar`. Introduce `l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hlN hb`. Take `⟨-, -, -, -, -, -, -, -, ⟨δ, hδ⟩, -⟩` from `hA`. Take `⟨b0, hb0, hne⟩` from `hb`. Establish `hl : l.Prime` using `Fact.out`.

Establish `hN0 : N ≠ 0` using `NeZero.ne N`. Establish `hNpos : 0 < N` using `Nat.pos_of_ne_zero hN0`. Establish `hdiam : ∀ (q : ℕ) (b : X.Fn l), X.diam N l q b = X.act l (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) b` using `fun q b => rfl`. Establish `hcop : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → q.Coprime N` using `fun q hq hd => (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hd (Dvd.dvd.mul_left h l))`. Establish `hisD : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → IsDiam N l q (sgD N l q)` using `fun q hq hd => Betti.isDiam_sgD hN0 hl.ne_zero (hcop q hq hd)`.

Establish `hpr : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b ∈ X.B N l (2 * e - 1), pr (X.act l (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) b) = δ q • pr b` using `fun q hq hd b hb => (hδ q hq hd b hb).2`. Establish `cancel : ∀ a a' : Qbar l, a • pr b0 = a' • pr b0 → a = a'` using `fun a a' h => smul_left_injective (Qbar l) hne h`. Establish `hQ : ∀ u : (ZMod N)ˣ, ∃ q > l * N, q.Prime ∧ (q : ZMod N) = u` using `fun u => Nat.forall_exists_prime_gt_and_eq_mod u.isUnit (l * N)`. Use `choose Q hQgt hQp hQu using hQ`. Establish `hQd : ∀ u, ¬ Q u ∣ l * N` using `fun u h => by`.

Establish `h1` using `Nat.le_of_dvd (Nat.mul_pos hl.pos hNpos) h`. Establish `h2` using `hQgt u`. Use linear arithmetic over natural numbers and integers. Establish `mem : ∀ u, sgD N l (Q u) ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l` using `fun u => (hisD _ (hQp u) (hQd u)).1`. Establish `en_u : ∀ u, (en (sgD N l (Q u)) 1 1 : ZMod N) = u` using `fun u => by`.

Rewrite using `[(hisD _ (hQp u) (hQd u)).2, hQu]`. Establish `inB : ∀ u (b : X.Fn l), b ∈ X.B N l (2 * e - 1) → X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l (2 * e - 1)` using `fun u b hb => (sBStab Ω ε X l N (2 * e - 1) hNpos b hb).2.1 _ (mem u)`. Establish `hΔ : ∀ u (b : X.Fn l), b ∈ X.B N l (2 * e - 1) → pr (X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b) = δ (Q u) • pr b` using `fun u b hb => hpr _ (hQp u) (hQd u) b hb`. Establish `formula : ∀ (q : ℕ) (u : (ZMod N)ˣ), q.Prime → ¬ q ∣ l * N → (u : ZMod N) = q → ∀ b ∈ X.B N l (2 * e - 1), pr (X.diam N l q b) = δ (Q u) • pr b`. Introduce `q u hq hd hu b hb`.

Establish `e1 : X.diam N l q b = X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b`. Rewrite using `[hdiam]`. Conclude with `dc_same X l N (2 * e - 1) _ _ (hisD q hq hd).1 (mem u) (by rw [(hisD q hq hd).2, en_u, hu]) b hb`. Rewrite using `[e1]`. Conclude with `hΔ u b hb`.

Establish `mul : ∀ u v, δ (Q (u * v)) = δ (Q u) * δ (Q v)`. Introduce `u v`. Apply `cancel` to reduce the goal to its premises. Establish `e2 : X.act l (((sgD N l (Q u) * sgD N l (Q v) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ) b0 = X.act l (sgD N l (Q (u * v)) : Matrix (Fin 2) (Fin 2) ℤ) b0` using `dc_same X l N (2 * e - 1) _ _ (Subgroup.mul_mem _ (mem u) (mem v)) (mem (u * v)) (by rw [dc_en N _ _ (mem u).1 (mem v).1, en_u, en_u, en_u, Units.val_mul]) b0 hb0`. Rewrite using `[← hΔ (u * v) b0 hb0, ← e2, ← dc_mul X l, hΔ v _ (inB u b0 hb0), hΔ u b0 hb0, smul_smul, mul_comm]`.

Establish `one : δ (Q 1) = 1`. Apply `cancel` to reduce the goal to its premises. Rewrite using `[one_smul, ← hΔ 1 b0 hb0]`. Establish `e3 : X.act l (sgD N l (Q 1) : Matrix (Fin 2) (Fin 2) ℤ) b0 = X.act l ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b0` using `dc_same X l N (2 * e - 1) _ _ (mem 1) (Subgroup.one_mem _) (by rw [en_u]; simp [en]) b0 hb0`. Rewrite using `[e3, dc_fix X l N (2 * e - 1) 1 (Subgroup.one_mem _) b0 hb0]`.

Establish `inv : ∀ u : (ZMod N)ˣ, δ (Q u) * δ (Q u⁻¹) = 1` using `fun u => by`. Rewrite using `[← mul, mul_inv_cancel, one]`. Use `⟨MonoidHom.mk' (fun u => Units.mkOfMulEqOne (δ (Q u)) (δ (Q u⁻¹)) (inv u)) (fun u v => by` and prove the remaining obligations. Use `ext`. Simplify using `[mul]), ?_⟩`.

Introduce `q u hq hd hu b hb`. Simplify using `only [MonoidHom.mk'_apply, Units.val_mkOfMulEqOne]`. Conclude with `formula q u hq hd hu b hb`.
-/
theorem UpperTheory.V.Z.Kato.Nb.sDiamChar :
    UpperTheory.V.Z.Kato.Nb.SDiamChar := by
  unfold SDiamChar
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hlN hb
  obtain ⟨-, -, -, -, -, -, -, -, ⟨δ, hδ⟩, -⟩ := hA
  obtain ⟨b0, hb0, hne⟩ := hb
  have hl : l.Prime := Fact.out
  have hN0 : N ≠ 0 := NeZero.ne N
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
  have hdiam : ∀ (q : ℕ) (b : X.Fn l),
      X.diam N l q b = X.act l (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) b := fun q b => rfl
  have hcop : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → q.Coprime N := fun q hq hd =>
    (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hd (Dvd.dvd.mul_left h l))
  have hisD : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → IsDiam N l q (sgD N l q) :=
    fun q hq hd => Betti.isDiam_sgD hN0 hl.ne_zero (hcop q hq hd)
  have hpr : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b ∈ X.B N l (2 * e - 1),
      pr (X.act l (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) b) = δ q • pr b :=
    fun q hq hd b hb => (hδ q hq hd b hb).2
  have cancel : ∀ a a' : Qbar l, a • pr b0 = a' • pr b0 → a = a' :=
    fun a a' h => smul_left_injective (Qbar l) hne h
  have hQ : ∀ u : (ZMod N)ˣ, ∃ q > l * N, q.Prime ∧ (q : ZMod N) = u :=
    fun u => Nat.forall_exists_prime_gt_and_eq_mod u.isUnit (l * N)
  choose Q hQgt hQp hQu using hQ
  have hQd : ∀ u, ¬ Q u ∣ l * N := fun u h => by
    have h1 := Nat.le_of_dvd (Nat.mul_pos hl.pos hNpos) h
    have h2 := hQgt u
    omega
  have mem : ∀ u, sgD N l (Q u) ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l :=
    fun u => (hisD _ (hQp u) (hQd u)).1
  have en_u : ∀ u, (en (sgD N l (Q u)) 1 1 : ZMod N) = u := fun u => by
    rw [(hisD _ (hQp u) (hQd u)).2, hQu]
  have inB : ∀ u (b : X.Fn l), b ∈ X.B N l (2 * e - 1) →
      X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l (2 * e - 1) :=
    fun u b hb => (sBStab Ω ε X l N (2 * e - 1) hNpos b hb).2.1 _ (mem u)
  have hΔ : ∀ u (b : X.Fn l), b ∈ X.B N l (2 * e - 1) →
      pr (X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b) = δ (Q u) • pr b :=
    fun u b hb => hpr _ (hQp u) (hQd u) b hb
  have formula : ∀ (q : ℕ) (u : (ZMod N)ˣ), q.Prime → ¬ q ∣ l * N → (u : ZMod N) = q →
      ∀ b ∈ X.B N l (2 * e - 1), pr (X.diam N l q b) = δ (Q u) • pr b := by
    intro q u hq hd hu b hb
    have e1 : X.diam N l q b = X.act l (sgD N l (Q u) : Matrix (Fin 2) (Fin 2) ℤ) b := by
      rw [hdiam]
      exact dc_same X l N (2 * e - 1) _ _ (hisD q hq hd).1 (mem u)
        (by rw [(hisD q hq hd).2, en_u, hu]) b hb
    rw [e1]
    exact hΔ u b hb
  have mul : ∀ u v, δ (Q (u * v)) = δ (Q u) * δ (Q v) := by
    intro u v
    apply cancel
    have e2 : X.act l (((sgD N l (Q u) * sgD N l (Q v) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ) b0 =
        X.act l (sgD N l (Q (u * v)) : Matrix (Fin 2) (Fin 2) ℤ) b0 :=
      dc_same X l N (2 * e - 1) _ _ (Subgroup.mul_mem _ (mem u) (mem v)) (mem (u * v))
        (by rw [dc_en N _ _ (mem u).1 (mem v).1, en_u, en_u, en_u, Units.val_mul]) b0 hb0
    rw [← hΔ (u * v) b0 hb0, ← e2, ← dc_mul X l, hΔ v _ (inB u b0 hb0), hΔ u b0 hb0, smul_smul, mul_comm]
  have one : δ (Q 1) = 1 := by
    apply cancel
    rw [one_smul, ← hΔ 1 b0 hb0]
    have e3 : X.act l (sgD N l (Q 1) : Matrix (Fin 2) (Fin 2) ℤ) b0 =
        X.act l ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b0 :=
      dc_same X l N (2 * e - 1) _ _ (mem 1) (Subgroup.one_mem _) (by rw [en_u]; simp [en]) b0 hb0
    rw [e3, dc_fix X l N (2 * e - 1) 1 (Subgroup.one_mem _) b0 hb0]
  have inv : ∀ u : (ZMod N)ˣ, δ (Q u) * δ (Q u⁻¹) = 1 := fun u => by
    rw [← mul, mul_inv_cancel, one]
  refine ⟨MonoidHom.mk' (fun u => Units.mkOfMulEqOne (δ (Q u)) (δ (Q u⁻¹)) (inv u))
    (fun u v => by
      ext
      simp [mul]), ?_⟩
  intro q u hq hd hu b hb
  simp only [MonoidHom.mk'_apply, Units.val_mkOfMulEqOne]
  exact formula q u hq hd hu b hb
