import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HeckeEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FinDim

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

noncomputable section

namespace UpperTheory.V.Br.EigenformExistence

/- English proof (translation)
Rewrite using `[strictPeriods_Gamma1]`. Conclude with `AddSubgroup.mem_zmultiples 1`.
-/
private theorem one_mem_per (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

/- English proof (translation)
Unfold `coef`. Rewrite using `[show ((c • f : CuspForm (Gamma1 N) k) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl, ModularForm.qExpansion_smul one_pos (one_mem_per N) c f]`. Simplify using the standard rewrite rules.
-/
private theorem coef_smul {N : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (c • f : CuspForm (Gamma1 N) k) n = c * coef f n := by
  unfold coef
  rw [show ((c • f : CuspForm (Gamma1 N) k) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl,
    ModularForm.qExpansion_smul one_pos (one_mem_per N) c f]
  simp

/- English proof (translation)
Unfold `coef`. Rewrite using `[← map_add]`. Use `congr 1`. Conclude with `ModularForm.qExpansion_add one_pos (one_mem_per N) f g`.
-/
private theorem coef_add {N : ℕ} {k : ℤ} (f g : CuspForm (Gamma1 N) k) (n : ℕ) :
    coef (f + g : CuspForm (Gamma1 N) k) n = coef f n + coef g n := by
  unfold coef
  rw [← map_add]
  congr 1
  exact ModularForm.qExpansion_add one_pos (one_mem_per N) f g

private def fT {K : Type} [Field K] (p : ℕ) (e : K) : Module.End K (ℕ → K) where
  toFun c n := c (p * n) + e * (if p ∣ n then c (n / p) else 0)
  map_add' c d := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : p ∣ n <;> simp [h] <;> ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem fT_apply {K : Type} [Field K] (p : ℕ) (e : K) (c : ℕ → K) (n : ℕ) :
    fT p e c n = c (p * n) + e * (if p ∣ n then c (n / p) else 0) := rfl

/- English proof (translation)
Establish `hc : Nat.Coprime p q` using `(Nat.coprime_primes hp hq).2 hpq`. Use function extensionality and compare the values at `n`. Simplify using `only [fT_apply]`. Establish `h1 : q ∣ p * n ↔ q ∣ n` using `hc.symm.dvd_mul_left`. Establish `h2 : p ∣ q * n ↔ p ∣ n` using `hc.dvd_mul_left`.

Apply the tactic sequence `by_cases a : p ∣ n <;> by_cases b : q ∣ n`. Take `⟨m, rfl⟩ : p * q ∣ n` from `hc.mul_dvd_of_dvd_of_dvd a b`. Establish `e1 : p * q * m / p = q * m` using `by rw [mul_assoc, Nat.mul_div_cancel_left _ hp.pos]`. Establish `e2 : p * q * m / q = p * m` using `by rw [mul_comm p q, mul_assoc, Nat.mul_div_cancel_left _ hq.pos]`. Simplify using `only [h1, h2, a, b, if_true, e1, e2, dvd_mul_right, Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hq.pos, Nat.mul_div_assoc _ a, Nat.mul_div_assoc _ b, mul_left_comm q p]`.

Expand and normalize the polynomial expressions, which then agree. Establish `b' : ¬ q ∣ n / p` using `fun h => b (h.trans (Nat.div_dvd_of_dvd a))`. Simplify using `only [h1, h2, a, b, b', if_true, if_false, Nat.mul_div_assoc _ a, mul_left_comm q p]`. Expand and normalize the polynomial expressions, which then agree. Establish `a' : ¬ p ∣ n / q` using `fun h => a (h.trans (Nat.div_dvd_of_dvd b))`.

Simplify using `only [h1, h2, a, b, a', if_true, if_false, Nat.mul_div_assoc _ b, mul_left_comm q p]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h1, h2, a, b, if_false, mul_left_comm q p]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem fT_comm {K : Type} [Field K] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e e' : K)
    (c : ℕ → K) : fT p e (fT q e' c) = fT q e' (fT p e c) := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  funext n
  simp only [fT_apply]
  have h1 : q ∣ p * n ↔ q ∣ n := hc.symm.dvd_mul_left
  have h2 : p ∣ q * n ↔ p ∣ n := hc.dvd_mul_left
  by_cases a : p ∣ n <;> by_cases b : q ∣ n
  · obtain ⟨m, rfl⟩ : p * q ∣ n := hc.mul_dvd_of_dvd_of_dvd a b
    have e1 : p * q * m / p = q * m := by rw [mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
    have e2 : p * q * m / q = p * m := by rw [mul_comm p q, mul_assoc, Nat.mul_div_cancel_left _ hq.pos]
    simp only [h1, h2, a, b, if_true, e1, e2, dvd_mul_right, Nat.mul_div_cancel_left _ hp.pos,
      Nat.mul_div_cancel_left _ hq.pos, Nat.mul_div_assoc _ a, Nat.mul_div_assoc _ b, mul_left_comm q p]
    ring
  · have b' : ¬ q ∣ n / p := fun h => b (h.trans (Nat.div_dvd_of_dvd a))
    simp only [h1, h2, a, b, b', if_true, if_false, Nat.mul_div_assoc _ a, mul_left_comm q p]
    ring
  · have a' : ¬ p ∣ n / q := fun h => a (h.trans (Nat.div_dvd_of_dvd b))
    simp only [h1, h2, a, b, a', if_true, if_false, Nat.mul_div_assoc _ b, mul_left_comm q p]
    ring
  · simp only [h1, h2, a, b, if_false, mul_left_comm q p]
    ring

/- English proof (translation)
Use function extensionality and compare the values at `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `h0`.

Distinguish the cases in `hn1 : n = 1`. Substitute `hn1` using the available equality. Conclude with `h1`. Take `⟨p, hp, m, rfl⟩` from `Nat.exists_prime_and_dvd hn1`. Establish `hm : 0 < m` using `Nat.pos_of_mul_pos_left hn`.

Establish `hlt : m < p * m` using `by nlinarith [hp.two_le]`. Use `congrFun (h ⟨p, hp⟩) m` as an intermediate fact. Establish `i1` using `ih m hlt`. Establish `i2` using `ih (m / p) ((Nat.div_le_self _ _).trans_lt hlt)`. Simplify using `only [Pi.zero_apply] at i1 i2`.

Simplify `this` using `[fT_apply, i1, i2]`.
-/
private theorem eq_zero_of_eig {K : Type} [Field K] (e b : Nat.Primes → K) (c : ℕ → K) (h0 : c 0 = 0) (h1 : c 1 = 0)
    (h : ∀ p : Nat.Primes, fT p.1 (e p) c = b p • c) : c = 0 := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact h0
    by_cases hn1 : n = 1
    · subst hn1; exact h1
    obtain ⟨p, hp, m, rfl⟩ := Nat.exists_prime_and_dvd hn1
    have hm : 0 < m := Nat.pos_of_mul_pos_left hn
    have hlt : m < p * m := by nlinarith [hp.two_le]
    have := congrFun (h ⟨p, hp⟩) m
    have i1 := ih m hlt
    have i2 := ih (m / p) ((Nat.div_le_self _ _).trans_lt hlt)
    simp only [Pi.zero_apply] at i1 i2
    simpa [fT_apply, i1, i2] using this

private def chSub (N k : ℕ) (χ : DirichletCharacter ℂ N) : Submodule ℂ (CuspForm (Gamma1 N) (k : ℤ)) where
  carrier := {g | HasChar k χ g}
  add_mem' := by
    intro f g hf hg γ hγ
    rw [show ((f + g : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = (f : ℍ → ℂ) + g from rfl, SlashAction.add_slash,
      hf γ hγ, hg γ hγ, smul_add]
  zero_mem' := by
    intro γ _
    rw [show ((0 : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = 0 from rfl, SlashAction.zero_slash, smul_zero]
  smul_mem' := by
    intro c f hf γ hγ
    rw [show ((c • f : CuspForm (Gamma1 N) (k : ℤ)) : ℍ → ℂ) = c • (f : ℍ → ℂ) from rfl, ModularForm.SL_smul_slash,
      hf γ hγ, smul_comm]

section
open Module
variable {K M : Type} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

end

private def Phi (N : ℕ) (k : ℤ) : CuspForm (Gamma1 N) k →ₗ[ℂ] (ℕ → ℂ) where
  toFun g n := if n = 0 then 0 else coef g n
  map_add' f g := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_add, Pi.add_apply, add_zero]
  map_smul' a f := by
    funext n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false, coef_smul, Pi.smul_apply, smul_eq_mul, mul_zero]
    rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem Phi_apply (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k) (n : ℕ) :
    Phi N k g n = if n = 0 then 0 else coef g n := rfl

/- English proof (translation)
Establish `h1 : p * n ≠ 0` using `mul_ne_zero hp.ne_zero (by omega)`. Rewrite using `[fT_apply, Phi_apply, if_neg h1]`. Distinguish the cases in `h : p ∣ n`. Establish `: n / p ≠ 0` using `(Nat.div_pos (Nat.le_of_dvd hn h) hp.pos).ne'`. Rewrite using `[if_pos h, if_pos h, Phi_apply, if_neg this]`.

Rewrite using `[if_neg h, if_neg h]`.
-/
private theorem fT_Phi (N : ℕ) (k : ℤ) (g : CuspForm (Gamma1 N) k)
    {p : ℕ} (hp : p.Prime) (e : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    fT p e (Phi N k g) n = coef g (p * n) + e * (if p ∣ n then coef g (n / p) else 0) := by
  have h1 : p * n ≠ 0 := mul_ne_zero hp.ne_zero (by omega)
  rw [fT_apply, Phi_apply, if_neg h1]
  by_cases h : p ∣ n
  · have : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn h) hp.pos).ne'
    rw [if_pos h, if_pos h, Phi_apply, if_neg this]
  · rw [if_neg h, if_neg h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h n hn`. Use `congrFun h n` as an intermediate fact. Rewrite `this` using `[fT_Phi N k g hp _ hn, Pi.smul_apply, Phi_apply, if_neg (show ¬ n = 0 by omega), smul_eq_mul]`. Then use the resulting hypothesis. Introduce `h`.

Use function extensionality and compare the values at `n`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `[fT_apply, Phi_apply]`. Rewrite using `[fT_Phi N k g hp _ hn, Pi.smul_apply, Phi_apply, if_neg hn.ne', smul_eq_mul]`. Conclude with `h n hn`.
-/
private theorem eig_iff (N k : ℕ) (χ : DirichletCharacter ℂ N) (g : CuspForm (Gamma1 N) (k : ℤ)) {p : ℕ} (hp : p.Prime) (c : ℂ) :
    fT p (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) (Phi N k g) = c • Phi N k g ↔ IsEigAt k χ g p c := by
  constructor
  · intro h n hn
    have := congrFun h n
    rwa [fT_Phi N k g hp _ hn, Pi.smul_apply, Phi_apply, if_neg (show ¬ n = 0 by omega), smul_eq_mul] at this
  · intro h
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [fT_apply, Phi_apply]
    · rw [fT_Phi N k g hp _ hn, Pi.smul_apply, Phi_apply, if_neg hn.ne', smul_eq_mul]
      exact h n hn

/- English proof (translation)
Use `haveI := (finDim N k).1`. Use `set V : Submodule ℂ (ℕ → ℂ) := (chSub N k χ).map (Phi N k) with hV`. Set `e : Nat.Primes → ℂ` to `fun p => χ ((p.1 : ℕ) : ZMod N) * ((p.1 : ℕ) : ℂ) ^ (k - 1)`. Establish `hmem : ∀ p : Nat.Primes, ∀ v ∈ V, fT p.1 (e p) v ∈ V`. Introduce and unpack `p _ ⟨g, hg, rfl⟩`.

Take `⟨g', hg', hc⟩` from `heckeEx N k hk χ g hg p.1 p.2`. Use `⟨g', hg', ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `n`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `[fT_apply, Phi_apply]`.

Rewrite using `[fT_Phi N k g p.2 _ hn, Phi_apply, if_neg hn.ne', hc n hn]`. Set `T : Nat.Primes → Module.End ℂ V` to `fun p => (fT p.1 (e p)).restrict (hmem p)`. Establish `hT : ∀ p (v : V), (T p v).1 = fT p.1 (e p) v.1` using `fun _ _ => rfl`. Establish `hc : ∀ p q, T p * T q = T q * T p`. Introduce `p q`.

Distinguish the cases in `hpq : p = q`. Rewrite using `[hpq]`. Use `ext1 v`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Module.End.mul_apply, hT]`.

Conclude with `fT_comm p.2 q.2 (fun h => hpq (Subtype.ext h)) _ _ _`. Set `U : Submodule ℂ V` to `⨅ p : {p : Nat.Primes // IsEigAt k χ f p.1 (a p.1)}, Module.End.eigenspace (T p.1) (a p.1.1)`. Establish `hU : ∀ v : V, v ∈ U ↔ ∀ p : Nat.Primes, IsEigAt k χ f p.1 (a p.1) → T p v = a p.1 • v` using `fun v => by`. Simplify using `only [U, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Subtype.forall]`. Take `⟨h, hhU, hne, heig⟩` from `UpperTheory.V.LinAlg.simEig T hc _ U rfl ((Submodule.ne_bot_iff U).2 ⟨⟨Phi N k f, f, hf, rfl⟩, (hU _).2 fun p hp => Subtype.ext ((eig_iff N k χ f p.2 _).2 hp), fun h0 => hf0 ((finDim N k).2 f fun n hn => by`.

Use `congrFun (congrArg Subtype.val h0) n` as an intermediate fact. Express the relevant statement in the definitionally equal form `Phi N k f n = 0 at this`. Rewrite using `[Phi_apply, if_neg (by omega)] at this)⟩)` and apply the resulting hypothesis. Use the proof step `(by`. Introduce `q x hx`.

Rewrite `hx`, the goal using `[hU]`. Introduce `p hp`. Establish `h2 : T p (T q x) = T q (T p x)` using `congrArg (fun S : Module.End ℂ V => S x) (hc p q)`. Rewrite using `[h2, hx p hp, map_smul])`. Use `choose b hb using heig`.

Establish `hab : ∀ p : Nat.Primes, IsEigAt k χ f p.1 (a p.1) → b p = a p.1` using `fun p hp => smul_left_injective ℂ hne ((hb p).symm.trans ((hU h).1 hhU p hp))`. Take `⟨_, g, hg, rfl⟩` from `h`. Establish `heig' : ∀ p : Nat.Primes, fT p.1 (e p) (Phi N k g) = b p • Phi N k g` using `fun p => congrArg Subtype.val (hb p)`. Establish `hg1 : coef g 1 ≠ 0`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `eq_zero_of_eig e b _ (by simp [Phi_apply]) (by simp [Phi_apply, h0]) heig'`. Establish `hE : ∀ p : Nat.Primes, IsEigAt k χ g p.1 (b p)` using `fun p => (eig_iff N k χ g p.2 _).1 (heig' p)`. Establish `hp : ∀ p : Nat.Primes, coef ((coef g 1)⁻¹ • g : CuspForm (Gamma1 N) (k : ℤ)) p.1 = b p`.

Introduce `p`. Use `hE p 1 le_rfl` as an intermediate fact. Rewrite `this` using `[if_neg p.2.not_dvd_one, mul_zero, add_zero, mul_one]`. Rewrite using `[coef_smul, this]`. Clear the denominators using the available nonvanishing facts.

Use `⟨⟨(coef g 1)⁻¹ • g, (chSub N k χ).smul_mem _ hg, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[coef_smul, inv_mul_cancel₀ hg1]`. Introduce `p hpp n hn`. Rewrite using `[hp ⟨p, hpp⟩]`. Use `hE ⟨p, hpp⟩ n hn` as an intermediate fact.

Simplify using `only [coef_smul]`. Use `split_ifs with hd`. Rewrite `this` using `[if_pos hd]`. Take the linear combination `(coef g 1)⁻¹ * this`. Rewrite `this` using `[if_neg hd]`.

Take the linear combination `(coef g 1)⁻¹ * this`. Introduce `p hpp h`. Conclude with `(hp ⟨p, hpp⟩).trans (hab ⟨p, hpp⟩ h)`.
-/
private theorem exists_eigenform (N k : ℕ) [NeZero N] (hk : 1 ≤ k) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) (k : ℤ)) (hf : HasChar k χ f) (hf0 : f ≠ 0) (a : ℕ → ℂ) :
    ∃ g : Eigenform k N χ, ∀ p : ℕ, p.Prime → IsEigAt k χ f p (a p) → g.a p = a p := by
  haveI := (finDim N k).1
  set V : Submodule ℂ (ℕ → ℂ) := (chSub N k χ).map (Phi N k) with hV
  let e : Nat.Primes → ℂ := fun p => χ ((p.1 : ℕ) : ZMod N) * ((p.1 : ℕ) : ℂ) ^ (k - 1)
  have hmem : ∀ p : Nat.Primes, ∀ v ∈ V, fT p.1 (e p) v ∈ V := by
    rintro p _ ⟨g, hg, rfl⟩
    obtain ⟨g', hg', hc⟩ := heckeEx N k hk χ g hg p.1 p.2
    refine ⟨g', hg', ?_⟩
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [fT_apply, Phi_apply]
    · rw [fT_Phi N k g p.2 _ hn, Phi_apply, if_neg hn.ne', hc n hn]
  let T : Nat.Primes → Module.End ℂ V := fun p => (fT p.1 (e p)).restrict (hmem p)
  have hT : ∀ p (v : V), (T p v).1 = fT p.1 (e p) v.1 := fun _ _ => rfl
  have hc : ∀ p q, T p * T q = T q * T p := by
    intro p q
    by_cases hpq : p = q
    · rw [hpq]
    · ext1 v
      apply Subtype.ext
      simp only [Module.End.mul_apply, hT]
      exact fT_comm p.2 q.2 (fun h => hpq (Subtype.ext h)) _ _ _
  let U : Submodule ℂ V := ⨅ p : {p : Nat.Primes // IsEigAt k χ f p.1 (a p.1)}, Module.End.eigenspace (T p.1) (a p.1.1)
  have hU : ∀ v : V, v ∈ U ↔ ∀ p : Nat.Primes, IsEigAt k χ f p.1 (a p.1) → T p v = a p.1 • v := fun v => by
    simp only [U, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Subtype.forall]
  obtain ⟨h, hhU, hne, heig⟩ := UpperTheory.V.LinAlg.simEig T hc _ U rfl
    ((Submodule.ne_bot_iff U).2 ⟨⟨Phi N k f, f, hf, rfl⟩,
      (hU _).2 fun p hp => Subtype.ext ((eig_iff N k χ f p.2 _).2 hp), fun h0 => hf0 ((finDim N k).2 f fun n hn => by
        have := congrFun (congrArg Subtype.val h0) n
        change Phi N k f n = 0 at this
        rwa [Phi_apply, if_neg (by omega)] at this)⟩)
    (by
      intro q x hx
      rw [hU] at hx ⊢
      intro p hp
      have h2 : T p (T q x) = T q (T p x) := congrArg (fun S : Module.End ℂ V => S x) (hc p q)
      rw [h2, hx p hp, map_smul])
  choose b hb using heig
  have hab : ∀ p : Nat.Primes, IsEigAt k χ f p.1 (a p.1) → b p = a p.1 := fun p hp =>
    smul_left_injective ℂ hne ((hb p).symm.trans ((hU h).1 hhU p hp))
  obtain ⟨_, g, hg, rfl⟩ := h
  have heig' : ∀ p : Nat.Primes, fT p.1 (e p) (Phi N k g) = b p • Phi N k g :=
    fun p => congrArg Subtype.val (hb p)
  have hg1 : coef g 1 ≠ 0 := by
    intro h0
    apply hne
    apply Subtype.ext
    exact eq_zero_of_eig e b _ (by simp [Phi_apply]) (by simp [Phi_apply, h0]) heig'
  have hE : ∀ p : Nat.Primes, IsEigAt k χ g p.1 (b p) := fun p => (eig_iff N k χ g p.2 _).1 (heig' p)
  have hp : ∀ p : Nat.Primes, coef ((coef g 1)⁻¹ • g : CuspForm (Gamma1 N) (k : ℤ)) p.1 = b p := by
    intro p
    have := hE p 1 le_rfl
    rw [if_neg p.2.not_dvd_one, mul_zero, add_zero, mul_one] at this
    rw [coef_smul, this]
    field_simp
  refine ⟨⟨(coef g 1)⁻¹ • g, (chSub N k χ).smul_mem _ hg, ?_, ?_⟩, ?_⟩
  · rw [coef_smul, inv_mul_cancel₀ hg1]
  · intro p hpp n hn
    rw [hp ⟨p, hpp⟩]
    have := hE ⟨p, hpp⟩ n hn
    simp only [coef_smul]
    split_ifs with hd
    · rw [if_pos hd] at this
      linear_combination (coef g 1)⁻¹ * this
    · rw [if_neg hd] at this
      linear_combination (coef g 1)⁻¹ * this
  · intro p hpp h
    exact (hp ⟨p, hpp⟩).trans (hab ⟨p, hpp⟩ h)
end UpperTheory.V.Br.EigenformExistence

/- English proof (translation)
Introduce `N k _ hk χ f hf hf0 a` and use `UpperTheory.V.Br.EigenformExistence.exists_eigenform N k hk χ f hf hf0 a`.
-/
theorem UpperTheory.V.Br.eigEx :
    UpperTheory.V.Br.EigEx :=
  fun N k _ hk χ f hf hf0 a => UpperTheory.V.Br.EigenformExistence.exists_eigenform N k hk χ f hf hf0 a

end
