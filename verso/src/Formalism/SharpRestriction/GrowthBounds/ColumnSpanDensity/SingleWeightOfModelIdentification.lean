import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SingleWeightLatticeComparison
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.HarProjEqZeroIff
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FinrankTensor

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility Formalism.CountingSumsFrames MvPolynomial

def RS.Ov {p n' : ℕ} (R : RS p n') : ValuationSubring R.Kf :=
  { (algebraMap R.O R.Kf).range with
    mem_or_inv_mem' := by
      intro x
      have := R.std.1.frac_O
      rcases ValuationRing.isInteger_or_isInteger R.O x with ⟨a, ha⟩ | ⟨a, ha⟩
      · exact Or.inl ⟨a, ha⟩
      · exact Or.inr ⟨a, ha⟩ }

/- English proof (translation)
Assemble the required witnesses or components as `⟨a, rfl⟩`.
-/
theorem RS.mem_Ov {p n' : ℕ} (R : RS p n') (a : R.O) : algebraMap R.O R.Kf a ∈ R.Ov.toSubring := ⟨a, rfl⟩

/- English proof (translation)
Introduce `n hn`. Establish `hcop : IsCoprime (n : ℤ) (p : ℤ)`. Use `(Nat.Prime.coprime_iff_not_dvd R.std.1.prime).2 hn` as an intermediate fact. Conclude with `(Nat.isCoprime_iff_coprime.2 this).symm`. Take `⟨a, b, hab⟩` from `hcop`.

Establish `hu : IsUnit (n : R.O)`. Assume the negation of the conclusion as `hnu`. Establish `h1 : (n : R.O) ∈ IsLocalRing.maximalIdeal R.O` using `(IsLocalRing.mem_maximalIdeal _).2 hnu`. Establish `h2 : (p : R.O) ∈ IsLocalRing.maximalIdeal R.O` using `(IsLocalRing.mem_maximalIdeal _).2 R.p_not_unit`. Establish `h3 : ((a : R.O) * (n : R.O) + (b : R.O) * (p : R.O)) ∈ IsLocalRing.maximalIdeal R.O` using `Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)`.

Establish `h4 : ((a : R.O) * (n : R.O) + (b : R.O) * (p : R.O)) = 1`. Use `congrArg (fun z : ℤ => (z : R.O)) hab` as an intermediate fact. Simplify using `using this`. Rewrite `h3` using `[h4]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 h3 isUnit_one`.

Take `⟨v, hv⟩` from `hu`. Use `⟨((v⁻¹ : R.Oˣ) : R.O), ?_⟩` and prove the remaining obligations. Establish `h5 : algebraMap R.O R.Kf ((v⁻¹ : R.Oˣ) : R.O) * (n : R.Kf) = 1`. Rewrite using `[← map_natCast (algebraMap R.O R.Kf) n, ← hv, ← map_mul, Units.inv_mul, map_one]`. Conclude with `eq_inv_of_mul_eq_one_left h5`.
-/
theorem RS.pLocal {p n' : ℕ} (R : RS p n') : PLocal R.Ov.toSubring p := by
  intro n hn
  have hcop : IsCoprime (n : ℤ) (p : ℤ) := by
    have := (Nat.Prime.coprime_iff_not_dvd R.std.1.prime).2 hn
    exact (Nat.isCoprime_iff_coprime.2 this).symm
  obtain ⟨a, b, hab⟩ := hcop
  have hu : IsUnit (n : R.O) := by
    by_contra hnu
    have h1 : (n : R.O) ∈ IsLocalRing.maximalIdeal R.O := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have h2 : (p : R.O) ∈ IsLocalRing.maximalIdeal R.O := (IsLocalRing.mem_maximalIdeal _).2 R.p_not_unit
    have h3 : ((a : R.O) * (n : R.O) + (b : R.O) * (p : R.O)) ∈ IsLocalRing.maximalIdeal R.O :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    have h4 : ((a : R.O) * (n : R.O) + (b : R.O) * (p : R.O)) = 1 := by
      have := congrArg (fun z : ℤ => (z : R.O)) hab
      simpa using this
    rw [h4] at h3
    exact (IsLocalRing.mem_maximalIdeal _).1 h3 isUnit_one
  obtain ⟨v, hv⟩ := hu
  refine ⟨((v⁻¹ : R.Oˣ) : R.O), ?_⟩
  have h5 : algebraMap R.O R.Kf ((v⁻¹ : R.Oˣ) : R.O) * (n : R.Kf) = 1 := by
    rw [← map_natCast (algebraMap R.O R.Kf) n, ← hv, ← map_mul, Units.inv_mul, map_one]
  exact eq_inv_of_mul_eq_one_left h5

def TwoLetterModelIdentification : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m →
    ∃ (α : ∀ P Q : ℕ, twoSp R.Kf m P Q ≃ₗ[R.Kf] PolAB R.Kf (m + 1) P Q)
      (β : ∀ a b : ℕ, PolAB R.Kf (m + 1) a b →ₗ[R.Kf] dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b))),
      (∀ a b, Function.Surjective (β a b)) ∧
      (∀ a b (f : PolAB R.Kf (m + 1) a b), β a b f = 0 ↔
        ∃ G ∈ PolAB R.Kf (m + 1) (a - 1) (b - 1), (f : PolXY R.Kf (m + 1)) = hXY R.Kf (m + 1) * G) ∧
      ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ → ∃ g' : GL (Fin (m + 1)) R.Kf,
        (∀ (P Q : ℕ) (x : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf), x ∈ twoLat R.O m P Q Λ ↔
          ∃ hx : x ∈ twoSp R.Kf m P Q,
            (α P Q ⟨x, hx⟩ : PolXY R.Kf (m + 1)) ∈ latOf g' (GaussLat R.Ov.toSubring)) ∧
        (∀ (a b : ℕ) (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf), y ∈ H0 R.O m (wtPQ m a b) Λ ↔
          ∃ f : PolAB R.Kf (m + 1) a b, (f : PolXY R.Kf (m + 1)) ∈ latOf g' (GaussLat R.Ov.toSubring) ∧
            (β a b f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) = y)

/- English proof (translation)
Establish `h1 : (Nat.log p (P + Q + (m + 1)) : ℝ) ≤ Real.logb p ((P + Q + (m + 1) : ℕ) : ℝ)` using `Real.natLog_le_logb _ _`. Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast hp`. Establish `h2 : Real.logb p ((P + Q + (m + 1) : ℕ) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + m)`. Apply `Real.logb_le_logb_of_le hp1` to reduce the goal to its premises. Establish `: 0 < P + Q + (m + 1)` using `by omega`.

Conclude with `this` after adjusting the coercions. Establish `: P + Q + (m + 1) ≤ 8 * a + m` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `h3 : (((m + 1 + 1) * Nat.log p (P + Q + (m + 1)) : ℕ) : ℝ) ≤ ((m : ℝ) + 2) * lgA p a m`. Unfold `lgA`.

Use `push_cast`. Establish `hm : (0 : ℝ) ≤ (m : ℝ) + 2` using `by positivity`. Establish `: ((m : ℝ) + 1 + 1) = (m : ℝ) + 2` using `by ring`. Rewrite using `[this]`. Conclude with `mul_le_mul_of_nonneg_left (by linarith) hm`.

Conclude with `le_trans h3 (Nat.le_ceil _)` after adjusting the coercions.
-/
theorem expo_le (p a m P Q : ℕ) (hp : 2 ≤ p) (h : P + Q + 1 ≤ 8 * a) :
    (m + 1 + 1) * Nat.log p (P + Q + (m + 1)) ≤ ⌈((m : ℝ) + 2) * lgA p a m⌉₊ := by
  have h1 : (Nat.log p (P + Q + (m + 1)) : ℝ) ≤ Real.logb p ((P + Q + (m + 1) : ℕ) : ℝ) := Real.natLog_le_logb _ _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have h2 : Real.logb p ((P + Q + (m + 1) : ℕ) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + m) := by
    apply Real.logb_le_logb_of_le hp1
    · have : 0 < P + Q + (m + 1) := by omega
      exact_mod_cast this
    · have : P + Q + (m + 1) ≤ 8 * a + m := by omega
      exact_mod_cast this
  have h3 : (((m + 1 + 1) * Nat.log p (P + Q + (m + 1)) : ℕ) : ℝ) ≤ ((m : ℝ) + 2) * lgA p a m := by
    unfold lgA
    push_cast
    have hm : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
    have : ((m : ℝ) + 1 + 1) = (m : ℝ) + 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hm
  exact_mod_cast le_trans h3 (Nat.le_ceil _)

/- English proof (translation)
Introduce `p n' R m hm a P Q hPQ`. Take `⟨α, β, hsurj, hker, hlat⟩` from `h p n' R m hm`. Establish `: CharZero R.Kf` using `R.charZero`. Establish `hp` using `R.std.1.prime`. Take `⟨io, pr, hsum, hL⟩` from `oneTop_abs R.Kf (m + 1) P Q p (by omega) hp R.Ov R.pLocal (α P Q) (fun j => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) (fun j => β (P - j) (Q - j)) (fun j => hsurj _ _) (fun j f => hker _ _ f)`.

Use `set E := (m + 1 + 1) * Nat.log p (P + Q + (m + 1)) with hE`. Use `set U := ⌈((m : ℝ) + 2) * lgA p a m⌉₊ with hU`. Establish `hEU : E ≤ U` using `expo_le p a m P Q hp.two_le hPQ`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le hEU`. Establish `hpd : (p : R.Kf) ^ d ∈ R.Ov.toSubring` using `Subring.pow_mem _ (natCast_mem _ p) d`.

Establish `hexI : ∀ j, ∃ I : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf, I ∘ₗ (dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))).subtype = (twoSp R.Kf m P Q).subtype ∘ₗ io j` using `fun j => LinearMap.exists_extend _`. Establish `hexP : ∀ j, ∃ Pj : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf, Pj ∘ₗ (twoSp R.Kf m P Q).subtype = (dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))).subtype ∘ₗ pr j` using `fun j => LinearMap.exists_extend _`. Use `choose I hI using hexI`. Use `choose Pj hPj using hexP`. Establish `hI' : ∀ j (y : dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))), I j (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) = (io j y : MvPolynomial _ R.Kf)` using `fun j y => LinearMap.congr_fun (hI j) y`.

Establish `hP' : ∀ j (x : twoSp R.Kf m P Q), Pj j (x : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf) = (pr j x : MvPolynomial _ R.Kf)` using `fun j x => LinearMap.congr_fun (hPj j) x`. Use `⟨I, Pj, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `h0` using `congrArg (twoSp R.Kf m P Q).subtype (hsum ⟨x, hx⟩)`. Rewrite `h0` using `[map_sum]`.

Combine the equalities or inequalities in the displayed calculation. Introduce `j _`. Use `⟨fun x hx => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hP' j ⟨x, hx⟩]`. Conclude with `(pr j ⟨x, hx⟩).2`.

Rewrite using `[hI' j ⟨y, hy⟩]`. Conclude with `(io j ⟨y, hy⟩).2`. Introduce `Λ hΛ j hj`. Take `⟨g', h1, h2⟩` from `hlat Λ hΛ`. Take `⟨hA, hB⟩` from `hL g' j hj`.

Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Take `⟨hx2, hx3⟩` from `(h1 P Q x).1 hx`. Take `⟨f, hf, hfe⟩` from `hA ⟨x, hx2⟩ hx3`. Use `(h2 (P - j) (Q - j) _).2 ⟨((p : R.Kf) ^ d) • f, smul_mem_latOf _ g' hpd hf, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul, hfe, hP' j ⟨x, hx2⟩, Submodule.coe_smul, Submodule.coe_smul, smul_smul, hd, pow_add, mul_comm]`. Introduce `y hy`. Take `⟨f, hf, hfe⟩` from `(h2 (P - j) (Q - j) y).1 hy`. Establish `h3` using `hB f hf`. Establish `hy2 : y ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))`.

Rewrite using `[← hfe]`. Conclude with `(β (P - j) (Q - j) f).2`. Establish `hyf : (⟨y, hy2⟩ : dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) = β (P - j) (Q - j) f` using `Subtype.ext hfe.symm`. Use `(h1 P Q _).2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hI' j ⟨y, hy2⟩]`.

Conclude with `Submodule.smul_mem _ _ (io j ⟨y, hy2⟩).2`. Establish `e : (⟨((p : R.Kf) ^ U) • I j y, by`. Rewrite using `[hI' j ⟨y, hy2⟩]`. Conclude with `Submodule.smul_mem _ _ (io j ⟨y, hy2⟩).2⟩ : twoSp R.Kf m P Q) =`. Use the proof step `((p : R.Kf) ^ d) • (((p : R.Kf) ^ E) • io j (β (P - j) (Q - j) f)) := by`.

Establish `hIy : I j y = (io j (β (P - j) (Q - j) f) : MvPolynomial _ R.Kf)`. Rewrite using `[← hyf]`. Conclude with `hI' j ⟨y, hy2⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((p : R.Kf) ^ U) • I j y = _`.

Rewrite using `[Submodule.coe_smul, Submodule.coe_smul, hIy, smul_smul, hd, pow_add, mul_comm]`. Rewrite using `[e, map_smul, Submodule.coe_smul]`. Conclude with `smul_mem_latOf _ g' hpd h3`.
-/
theorem single_weight_of_model_identification (h : TwoLetterModelIdentification) : SingleWeightLatticeComparison := by
  classical
  intro p n' R m hm a P Q hPQ
  obtain ⟨α, β, hsurj, hker, hlat⟩ := h p n' R m hm
  have : CharZero R.Kf := R.charZero
  have hp := R.std.1.prime
  obtain ⟨io, pr, hsum, hL⟩ := oneTop_abs R.Kf (m + 1) P Q p (by omega) hp R.Ov R.pLocal (α P Q)
    (fun j => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) (fun j => β (P - j) (Q - j))
    (fun j => hsurj _ _) (fun j f => hker _ _ f)
  set E := (m + 1 + 1) * Nat.log p (P + Q + (m + 1)) with hE
  set U := ⌈((m : ℝ) + 2) * lgA p a m⌉₊ with hU
  have hEU : E ≤ U := expo_le p a m P Q hp.two_le hPQ
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hEU
  have hpd : (p : R.Kf) ^ d ∈ R.Ov.toSubring := Subring.pow_mem _ (natCast_mem _ p) d
  have hexI : ∀ j, ∃ I : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf,
      I ∘ₗ (dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))).subtype =
        (twoSp R.Kf m P Q).subtype ∘ₗ io j := fun j => LinearMap.exists_extend _
  have hexP : ∀ j, ∃ Pj : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf,
      Pj ∘ₗ (twoSp R.Kf m P Q).subtype =
        (dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))).subtype ∘ₗ pr j :=
    fun j => LinearMap.exists_extend _
  choose I hI using hexI
  choose Pj hPj using hexP
  have hI' : ∀ j (y : dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))),
      I j (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) = (io j y : MvPolynomial _ R.Kf) :=
    fun j y => LinearMap.congr_fun (hI j) y
  have hP' : ∀ j (x : twoSp R.Kf m P Q),
      Pj j (x : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf) = (pr j x : MvPolynomial _ R.Kf) :=
    fun j x => LinearMap.congr_fun (hPj j) x
  refine ⟨I, Pj, ?_, ?_, ?_⟩
  · intro x hx
    have h0 := congrArg (twoSp R.Kf m P Q).subtype (hsum ⟨x, hx⟩)
    rw [map_sum] at h0
    calc ∑ j ∈ Finset.range (min P Q + 1), I j (Pj j x)
        = ∑ j ∈ Finset.range (min P Q + 1), (twoSp R.Kf m P Q).subtype (io j (pr j ⟨x, hx⟩)) :=
          Finset.sum_congr rfl fun j _ => by rw [hP' j ⟨x, hx⟩, hI']; rfl
      _ = x := h0
  · intro j _
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · rw [hP' j ⟨x, hx⟩]; exact (pr j ⟨x, hx⟩).2
    · rw [hI' j ⟨y, hy⟩]; exact (io j ⟨y, hy⟩).2
  · intro Λ hΛ j hj
    obtain ⟨g', h1, h2⟩ := hlat Λ hΛ
    obtain ⟨hA, hB⟩ := hL g' j hj
    constructor
    · intro x hx
      obtain ⟨hx2, hx3⟩ := (h1 P Q x).1 hx
      obtain ⟨f, hf, hfe⟩ := hA ⟨x, hx2⟩ hx3
      refine (h2 (P - j) (Q - j) _).2 ⟨((p : R.Kf) ^ d) • f, smul_mem_latOf _ g' hpd hf, ?_⟩
      rw [map_smul, hfe, hP' j ⟨x, hx2⟩, Submodule.coe_smul, Submodule.coe_smul, smul_smul, hd, pow_add, mul_comm]
    · intro y hy
      obtain ⟨f, hf, hfe⟩ := (h2 (P - j) (Q - j) y).1 hy
      have h3 := hB f hf
      have hy2 : y ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j))) := by
        rw [← hfe]; exact (β (P - j) (Q - j) f).2
      have hyf : (⟨y, hy2⟩ : dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) = β (P - j) (Q - j) f :=
        Subtype.ext hfe.symm
      refine (h1 P Q _).2 ⟨?_, ?_⟩
      · rw [hI' j ⟨y, hy2⟩]
        exact Submodule.smul_mem _ _ (io j ⟨y, hy2⟩).2
      · have e : (⟨((p : R.Kf) ^ U) • I j y, by
            rw [hI' j ⟨y, hy2⟩]; exact Submodule.smul_mem _ _ (io j ⟨y, hy2⟩).2⟩ : twoSp R.Kf m P Q) =
            ((p : R.Kf) ^ d) • (((p : R.Kf) ^ E) • io j (β (P - j) (Q - j) f)) := by
          have hIy : I j y = (io j (β (P - j) (Q - j) f) : MvPolynomial _ R.Kf) := by
            rw [← hyf]; exact hI' j ⟨y, hy2⟩
          apply Subtype.ext
          show ((p : R.Kf) ^ U) • I j y = _
          rw [Submodule.coe_smul, Submodule.coe_smul, hIy, smul_smul, hd, pow_add, mul_comm]
        rw [e, map_smul, Submodule.coe_smul]
        exact smul_mem_latOf _ g' hpd h3

end Formalism.MainNotions.flipOneThree.Pf

end
