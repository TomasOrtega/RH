import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PassPoly

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C a => intro x hx`. Simplify `D.smul_mem a hx` using `[Module.algebraMap_end_apply]`. Consider the case `add p q hp hq => intro x hx`. Simplify using `using D.add_mem (hp x hx) (hq x hx)`.

Consider the case `monomial n a ih`. Introduce `x hx`. Use `ih _ (hD x hx)` as an intermediate fact. Rewrite using `[pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X]`. Conclude with `this`.
-/
theorem aeval_mem_of_stable {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (p : L[X]) : ∀ x ∈ D, Polynomial.aeval f p x ∈ D := by
  induction p using Polynomial.induction_on with
  | C a => intro x hx; simpa [Module.algebraMap_end_apply] using D.smul_mem a hx
  | add p q hp hq => intro x hx; simpa using D.add_mem (hp x hx) (hq x hx)
  | monomial n a ih =>
    intro x hx
    have := ih _ (hD x hx)
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    exact this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _ d _ h`. Simplify using `at h`. Simplify using `[h]`. Consider the case `insert a t hat ih`.

Introduce `hinj d hd h`. Rewrite `h` using `[Finset.prod_insert hat]`. Establish `hcop : IsCoprime (X - C (c a)) (∏ b ∈ t, (X - C (c b)))`. Use `IsCoprime.prod_right fun b hb => ?_` and prove the remaining obligations. Use `Polynomial.isCoprime_X_sub_C_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.2 fun e => hat ?_))` and prove the remaining obligations.

Rewrite using `[hinj a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb) e]`. Conclude with `hb`. Take `⟨u, v, huv⟩` from `hcop`. Use `set Q := ∏ b ∈ t, (X - C (c b)) with hQ`. Establish `hdec : d = Polynomial.aeval f (u * (X - C (c a))) d + Polynomial.aeval f (v * Q) d`.

Rewrite using `[← LinearMap.add_apply, ← map_add, huv, map_one, Module.End.one_apply]`. Rewrite using `[Finset.iSup_insert, hdec, add_comm]`. Use `Submodule.add_mem_sup ?_ ?_` and prove the remaining obligations. Use `⟨aeval_mem_of_stable f D hD _ d hd, ?_⟩` and prove the remaining obligations. Establish `h1 : Polynomial.aeval f (X - C (c a)) (Polynomial.aeval f (v * Q) d) = 0`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, show (X - C (c a)) * (v * Q) = v * ((X - C (c a)) * Q) by ring, map_mul, Module.End.mul_apply, h, map_zero]`. Simplify `h1` using `[Module.algebraMap_end_apply]`. Use `ih (fun x hx y hy => hinj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)) _ (aeval_mem_of_stable f D hD _ d hd) ?_` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul, show Q * (u * (X - C (c a))) = u * ((X - C (c a)) * Q) by ring, map_mul, Module.End.mul_apply, h, map_zero]`.
-/
theorem mem_iSup_eigen {L M ι : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (c : ι → L) (s : Finset ι) :
    (∀ a ∈ s, ∀ b ∈ s, c a = c b → a = b) → ∀ d ∈ D,
      Polynomial.aeval f (∏ a ∈ s, (X - C (c a))) d = 0 →
      d ∈ ⨆ a ∈ s, (D ⊓ LinearMap.ker (f - c a • LinearMap.id)) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _ d _ h; simp at h; simp [h]
  | insert a t hat ih =>
    intro hinj d hd h
    rw [Finset.prod_insert hat] at h
    have hcop : IsCoprime (X - C (c a)) (∏ b ∈ t, (X - C (c b))) := by
      refine IsCoprime.prod_right fun b hb => ?_
      refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.2 fun e => hat ?_))
      rw [hinj a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb) e]
      exact hb
    obtain ⟨u, v, huv⟩ := hcop
    set Q := ∏ b ∈ t, (X - C (c b)) with hQ
    have hdec : d = Polynomial.aeval f (u * (X - C (c a))) d + Polynomial.aeval f (v * Q) d := by
      rw [← LinearMap.add_apply, ← map_add, huv, map_one, Module.End.one_apply]
    rw [Finset.iSup_insert, hdec, add_comm]
    refine Submodule.add_mem_sup ?_ ?_
    · refine ⟨aeval_mem_of_stable f D hD _ d hd, ?_⟩
      have h1 : Polynomial.aeval f (X - C (c a)) (Polynomial.aeval f (v * Q) d) = 0 := by
        rw [← Module.End.mul_apply, ← map_mul,
          show (X - C (c a)) * (v * Q) = v * ((X - C (c a)) * Q) by ring, map_mul,
          Module.End.mul_apply, h, map_zero]
      simpa [Module.algebraMap_end_apply] using h1
    · refine ih (fun x hx y hy => hinj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)) _
        (aeval_mem_of_stable f D hD _ d hd) ?_
      rw [← Module.End.mul_apply, ← map_mul,
          show Q * (u * (X - C (c a))) = u * ((X - C (c a)) * Q) by ring, map_mul,
          Module.End.mul_apply, h, map_zero]

section
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [actVB]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem actVB_mul' (g h : G) (x : V ⊗[Qp] B) :
    actVB PC.PD ρ (g * h) x = actVB PC.PD ρ g (actVB PC.PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [actVB]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem actVB_one' (x : V ⊗[Qp] B) : actVB PC.PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [actVB, PotCrysData.resH, PC.actB_eq]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem actVB_resH (h : PC.H) (x : V ⊗[Qp] B) :
    actVB PC.PD' (PC.resH ρ) h x = actVB PC.PD ρ (h : G) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, PotCrysData.resH, PC.actB_eq]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Simplify using `only [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, actVB_resH, Subtype.forall]`.
-/
theorem mem_Dpcris_iff (x : V ⊗[Qp] B) :
    x ∈ PC.Dpcris ρ ↔ ∀ g ∈ PC.H, actVB PC.PD ρ g x = x := by
  simp only [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, actVB_resH, Subtype.forall]

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[mem_Dpcris_iff]`. Introduce `h hh`. Establish `h1 : g⁻¹ * h * g ∈ PC.H` using `by simpa using PC.normal.conj_mem h hh g⁻¹`. Rewrite using `[← actVB_mul', show h * g = g * (g⁻¹ * h * g) by group, actVB_mul', hx _ h1]`.
-/
theorem Dpcris_stable (g : G) : ∀ x ∈ PC.Dpcris ρ, actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  intro x hx
  rw [mem_Dpcris_iff] at hx ⊢
  intro h hh
  have h1 : g⁻¹ * h * g ∈ PC.H := by simpa using PC.normal.conj_mem h hh g⁻¹
  rw [← actVB_mul', show h * g = g * (g⁻¹ * h * g) by group, actVB_mul', hx _ h1]

/- English proof (translation)
Use `⟨h1, h2, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Take `⟨γ, hsep, hgen⟩` from `h4`. Introduce `d hd`. Use `mem_iSup_eigen (actVB PC.PD ρ (γ : G)) (PC.Dpcris ρ) (Dpcris_stable PC ρ γ) (fun a : PC.Iner →* LLˣ => ((a γ : LLˣ) : LL)) Sig (fun a ha b hb e => hsep a ha b hb (Units.ext e)) d hd (h3 γ d hd)` as an intermediate fact. Use `(iSup₂_mono (fun a ha => ?_) : _ ≤ ⨆ a ∈ Sig, PC.Eig ρ PC.Iner a) this` and prove the remaining obligations.

Introduce and unpack `x ⟨hx, hx'⟩`. Use `⟨hx, ?_⟩` and prove the remaining obligations. Establish `hγ : actVB PC.PD ρ (γ : G) x = ((a γ : LLˣ) : LL) • x`. Simplify `hx'` using `[sub_eq_zero]`. Establish `hn : ∀ n : ℕ, actVB PC.PD ρ ((γ : G) ^ n) x = ((a γ : LLˣ) : LL) ^ n • x`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [actVB_one']`. Consider the case `succ n ih => rw [pow_succ, actVB_mul', hγ, map_smul, ih, smul_smul, pow_succ, mul_comm]`. Simplify using `only [Submodule.coe_iInf, Set.mem_iInter, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`.

Introduce `g`. Take `⟨n, u, hu, rfl⟩` from `hgen g`. Rewrite using `[map_mul, h1 a ha u hu, mul_one, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, actVB_mul', (mem_Dpcris_iff PC ρ x).1 hx u hu, hn, Units.val_pow_eq_pow_val]`. Conclude with `iSup₂_le fun a _ => inf_le_left`.
-/
theorem inertiaThrough_of_poly (Sig : Finset (PC.Iner →* LLˣ))
    (h1 : ∀ a ∈ Sig, ∀ g : PC.Iner, (g : G) ∈ PC.H → a g = 1)
    (h2 : ∀ a ∈ Sig, Nat.Coprime (orderOf a) PC.PD.p)
    (h3 : ∀ (g : PC.Iner), ∀ d ∈ PC.Dpcris ρ, (Polynomial.aeval (actVB PC.PD ρ (g : G))
      (∏ a ∈ Sig, (X - C ((a g : LLˣ) : LL)))) d = 0)
    (h4 : ∃ γ : PC.Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧
      ∀ g : PC.Iner, ∃ (n : ℕ) (u : PC.Iner), ((u : G) ∈ PC.H) ∧ g = γ ^ n * u) :
    PC.InertiaThrough ρ Sig := by
  refine ⟨h1, h2, le_antisymm ?_ ?_⟩
  · obtain ⟨γ, hsep, hgen⟩ := h4
    intro d hd
    have := mem_iSup_eigen (actVB PC.PD ρ (γ : G)) (PC.Dpcris ρ) (Dpcris_stable PC ρ γ)
      (fun a : PC.Iner →* LLˣ => ((a γ : LLˣ) : LL)) Sig
      (fun a ha b hb e => hsep a ha b hb (Units.ext e)) d hd (h3 γ d hd)
    refine (iSup₂_mono (fun a ha => ?_) : _ ≤ ⨆ a ∈ Sig, PC.Eig ρ PC.Iner a) this
    rintro x ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have hγ : actVB PC.PD ρ (γ : G) x = ((a γ : LLˣ) : LL) • x := by
      simpa [sub_eq_zero] using hx'
    have hn : ∀ n : ℕ, actVB PC.PD ρ ((γ : G) ^ n) x = ((a γ : LLˣ) : LL) ^ n • x := by
      intro n
      induction n with
      | zero => simp [actVB_one']
      | succ n ih => rw [pow_succ, actVB_mul', hγ, map_smul, ih, smul_smul, pow_succ, mul_comm]
    simp only [Submodule.coe_iInf, Set.mem_iInter, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro g
    obtain ⟨n, u, hu, rfl⟩ := hgen g
    rw [map_mul, h1 a ha u hu, mul_one, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, actVB_mul',
      (mem_Dpcris_iff PC ρ x).1 hx u hu, hn, Units.val_pow_eq_pow_val]
  · exact iSup₂_le fun a _ => inf_le_left

end

/- English proof (translation)
Introduce `l _ P K K' LL h hN hF hS V _ _ _ _ ρ Sig h1 h2 h3 h4`. Use `inertiaThrough_of_poly (pc P h hN hF hS) ρ Sig h1 ?_ h3 h4` and prove the remaining obligations. Establish `hp : (pc P h hN hF hS).PD.p = l` using `P.PD_p K`. Rewrite using `[hp]`. Conclude with `h2`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)), (∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1) → (∀ a ∈ Sig, Nat.Coprime (orderOf a) l) → (∀ (g : (pc P h hN hF hS).Iner), ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, (Polynomial.aeval (actVB (P.PD K) ρ (g : ↥(GK K))) (∏ a ∈ Sig, (X - C ((a g : (↥LL.1)ˣ) : ↥LL.1)))) d = 0) → (∃ γ : (pc P h hN hF hS).Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧ ∀ g : (pc P h hN hF hS).Iner, ∃ (n : ℕ) (u : (pc P h hN hF hS).Iner), ((u : ↥(GK K)) ∈ (pc P h hN hF hS).H) ∧ g = γ ^ n * u) → (pc P h hN hF hS).InertiaThrough ρ Sig := by
  intro l _ P K K' LL h hN hF hS V _ _ _ _ ρ Sig h1 h2 h3 h4
  refine inertiaThrough_of_poly (pc P h hN hF hS) ρ Sig h1 ?_ h3 h4
  have hp : (pc P h hN hF hS).PD.p = l := P.PD_p K
  rw [hp]
  exact h2

end GlobalTheory.PassPoly

end
