import Mathlib

noncomputable section

namespace PositivityTheory.Rg.Rs.SliceClasses

section Fixed

variable {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] {ι : Type*}

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro v hv`. Simplify using `using hv`. Consider the case `succ k ih => intro v hv`.

Rewrite using `[pow_succ', Module.End.mul_apply]`. Conclude with `hf _ (ih v hv)`.
-/
theorem C_pow_mem {P : Submodule ℂ U} {f : Module.End ℂ U} (hf : ∀ v ∈ P, f v ∈ P) :
    ∀ k : ℕ, ∀ v ∈ P, (f ^ k) v ∈ P := by
  intro k
  induction k with
  | zero => intro v hv; simpa using hv
  | succ k ih => intro v hv; rw [pow_succ', Module.End.mul_apply]; exact hf _ (ih v hv)

/- English proof (translation)
Introduce `v hv` and use `by rw [LinearMap.sub_apply, Module.End.one_apply]; exact P.sub_mem (hf v hv) hv`.
-/
theorem C_sub_one_mem {P : Submodule ℂ U} {f : Module.End ℂ U} (hf : ∀ v ∈ P, f v ∈ P) :
    ∀ v ∈ P, (f - 1) v ∈ P := fun v hv => by
  rw [LinearMap.sub_apply, Module.End.one_apply]; exact P.sub_mem (hf v hv) hv

/- English proof (translation)
Establish `h : Commute (M j) ((M i - 1) ^ k)` using `((hc j i).sub_right (Commute.one_right _)).pow_right k`. Rewrite using `[← Module.End.mul_apply, h.eq, Module.End.mul_apply]`.
-/
theorem C_comm_pow {M : ι → Module.End ℂ U} (hc : ∀ i j, Commute (M i) (M j)) (i j : ι) (k : ℕ) (x : U) :
    M j (((M i - 1) ^ k) x) = ((M i - 1) ^ k) (M j x) := by
  have h : Commute (M j) ((M i - 1) ^ k) := ((hc j i).sub_right (Commute.one_right _)).pow_right k
  rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `P hn hP hst hnil`. Distinguish the cases in `hall : ∀ i, ∀ v ∈ P, M i v = v`.

Take `⟨v, hv, hv0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP`. Conclude with `⟨v, hv, hv0, fun i => hall i v hv⟩`. Use `push Not at hall`. Take `⟨i, v, hv, hMv⟩` from `hall`. Use `set P' : Submodule ℂ U := P ⊓ LinearMap.ker (M i - 1) with hP'def`.

Establish `hlt : P' < P`. Use `lt_of_le_of_ne inf_le_left fun h => hMv ?_` and prove the remaining obligations. Establish `h2 : v ∈ P'` using `h ▸ hv`. Establish `h3` using `(Submodule.mem_inf.1 h2).2`. Rewrite `h3` using `[LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]`.

Conclude with `h3`. Establish `hne : P' ≠ ⊥`. Take `⟨u, hu, hu0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP`. Establish `hex : ∃ k, (((M i - 1) ^ k : Module.End ℂ U)) u = 0` using `hnil i u hu`. Establish `hkk : ((M i - 1) ^ Nat.find hex) u = 0` using `Nat.find_spec hex`.

Establish `hkk0 : Nat.find hex ≠ 0`. Introduce `h0`. Rewrite `hkk` using `[h0, pow_zero, Module.End.one_apply]`. Conclude with `hu0 hkk`. Take `⟨j, hj⟩` from `Nat.exists_eq_succ_of_ne_zero hkk0`.

Establish `hmin : ((M i - 1) ^ j) u ≠ 0` using `Nat.find_min hex (by omega)`. Use `(Submodule.ne_bot_iff _).2 ⟨((M i - 1) ^ j) u, Submodule.mem_inf.2 ⟨?_, ?_⟩, hmin⟩` and prove the remaining obligations. Conclude with `C_pow_mem (C_sub_one_mem (hst i)) j u hu`. Rewrite using `[LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ', show j + 1 = Nat.find hex by omega]; exact hkk`. Establish `hst' : ∀ l, ∀ x ∈ P', M l x ∈ P'`.

Introduce `l x hx`. Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.1 hx`. Use `Submodule.mem_inf.2 ⟨hst l x hx1, ?_⟩` and prove the remaining obligations. Rewrite `hx2`, the goal using `[LinearMap.mem_ker]`. Use `C_comm_pow hc i l 1 x` as an intermediate fact.

Rewrite `this` using `[pow_one]`. Rewrite using `[← this, hx2, map_zero]`. Establish `hnil' : ∀ l, ∀ x ∈ P', ∃ k : ℕ, ((M l - 1) ^ k) x = 0` using `fun l x hx => hnil l x (Submodule.mem_inf.1 hx).1`. Take `⟨w, hw, hw0, hfix⟩` from `ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) P' rfl hne hst' hnil'`. Conclude with `⟨w, (Submodule.mem_inf.1 hw).1, hw0, hfix⟩`.
-/
theorem C_nil (M : ι → Module.End ℂ U) (hc : ∀ i j, Commute (M i) (M j)) :
    ∀ (n : ℕ) (P : Submodule ℂ U), Module.finrank ℂ P = n → P ≠ ⊥ → (∀ i, ∀ v ∈ P, M i v ∈ P) →
      (∀ i, ∀ v ∈ P, ∃ k : ℕ, ((M i - 1) ^ k) v = 0) → ∃ w ∈ P, w ≠ 0 ∧ ∀ i, M i w = w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP hst hnil
  by_cases hall : ∀ i, ∀ v ∈ P, M i v = v
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    exact ⟨v, hv, hv0, fun i => hall i v hv⟩
  push Not at hall
  obtain ⟨i, v, hv, hMv⟩ := hall
  classical
  set P' : Submodule ℂ U := P ⊓ LinearMap.ker (M i - 1) with hP'def
  have hlt : P' < P := by
    refine lt_of_le_of_ne inf_le_left fun h => hMv ?_
    have h2 : v ∈ P' := h ▸ hv
    have h3 := (Submodule.mem_inf.1 h2).2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h3
    exact h3
  have hne : P' ≠ ⊥ := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hex : ∃ k, (((M i - 1) ^ k : Module.End ℂ U)) u = 0 := hnil i u hu
    have hkk : ((M i - 1) ^ Nat.find hex) u = 0 := Nat.find_spec hex
    have hkk0 : Nat.find hex ≠ 0 := by
      intro h0; rw [h0, pow_zero, Module.End.one_apply] at hkk; exact hu0 hkk
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hkk0
    have hmin : ((M i - 1) ^ j) u ≠ 0 := Nat.find_min hex (by omega)
    refine (Submodule.ne_bot_iff _).2 ⟨((M i - 1) ^ j) u, Submodule.mem_inf.2 ⟨?_, ?_⟩, hmin⟩
    · exact C_pow_mem (C_sub_one_mem (hst i)) j u hu
    · rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ', show j + 1 = Nat.find hex by omega]; exact hkk
  have hst' : ∀ l, ∀ x ∈ P', M l x ∈ P' := by
    intro l x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨hst l x hx1, ?_⟩
    rw [LinearMap.mem_ker] at hx2 ⊢
    have := C_comm_pow hc i l 1 x
    rw [pow_one] at this
    rw [← this, hx2, map_zero]
  have hnil' : ∀ l, ∀ x ∈ P', ∃ k : ℕ, ((M l - 1) ^ k) x = 0 := fun l x hx =>
    hnil l x (Submodule.mem_inf.1 hx).1
  obtain ⟨w, hw, hw0, hfix⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) P' rfl hne hst' hnil'
  exact ⟨w, (Submodule.mem_inf.1 hw).1, hw0, hfix⟩

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules. Consider the case `succ m ih => intro x`.

Rewrite using `[pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, pow_succ', Module.End.mul_apply]`.
-/
theorem C_restrict_pow {P : Submodule ℂ U} {f : Module.End ℂ U} (hf : ∀ v ∈ P, f v ∈ P) :
    ∀ (m : ℕ) (x : P), (((f.restrict hf) ^ m) x : U) = (f ^ m) (x : U) := by
  intro m
  induction m with
  | zero => intro x; simp
  | succ m ih => intro x; rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ih, pow_succ',
      Module.End.mul_apply]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `P hn hst hinv hv`. Take `⟨v, hv, hΦv⟩` from `hv`.

Distinguish the cases in `hnil : ∀ i, ∀ u ∈ P, ∃ k : ℕ, ((M i - 1) ^ k) u = 0`. Use `C_nil M hc _ P rfl ?_ hst hnil` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hv` using `[Submodule.mem_bot]`. Conclude with `hΦv (by rw [hv, map_zero])`.

Use `push Not at hnil`. Take `⟨i, u, hu, hku⟩` from `hnil`. Establish `hgP : ∀ x ∈ P, (M i - 1) x ∈ P` using `C_sub_one_mem (hst i)`. Take `⟨m, hm, hm1⟩` from `((LinearMap.eventually_isCompl_ker_pow_range_pow ((M i - 1).restrict hgP)).and (Filter.eventually_ge_atTop 1)).exists`. Use `set Q : Submodule ℂ U := P ⊓ LinearMap.ker ((M i - 1) ^ m) with hQdef`.

Take `⟨k, hk, r, hr, hkr⟩` from `Submodule.mem_sup.1 (hm.sup_eq_top ▸ Submodule.mem_top (x := (⟨v, hv⟩ : P)))`. Establish `hΦr : Φ (r : U) = 0`. Take `⟨y, hy⟩` from `LinearMap.mem_range.1 hr`. Take `⟨m', rfl⟩` from `Nat.exists_eq_add_of_le hm1`. Rewrite using `[← hy, C_restrict_pow hgP, add_comm, pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub, hinv i _ (C_pow_mem hgP m' _ y.2), sub_self]`.

Establish `hkv : (k : U) + r = v` using `congrArg Subtype.val hkr`. Establish `hΦk : Φ (k : U) ≠ 0`. Introduce `h0`. Apply `hΦv` to reduce the goal to its premises. Rewrite using `[← hkv, map_add, h0, hΦr, add_zero]`.

Establish `hkQ : (k : U) ∈ Q`. Use `Submodule.mem_inf.2 ⟨k.2, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, ← C_restrict_pow hgP, LinearMap.mem_ker.1 hk, Submodule.coe_zero]`. Establish `hlt : Q < P`. Use `lt_of_le_of_ne inf_le_left fun h => hku m ?_` and prove the remaining obligations.

Establish `h2 : u ∈ Q` using `h ▸ hu`. Conclude with `(Submodule.mem_inf.1 h2).2`. Establish `hstQ : ∀ l, ∀ x ∈ Q, M l x ∈ Q`. Introduce `l x hx`. Take `⟨hx1, hx2⟩` from `Submodule.mem_inf.1 hx`.

Use `Submodule.mem_inf.2 ⟨hst l x hx1, ?_⟩` and prove the remaining obligations. Rewrite `hx2`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[← C_comm_pow hc i l m x, hx2, map_zero]`. Take `⟨w, hw, hw0, hfix⟩` from `ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) Q rfl hstQ (fun l x hx => hinv l x (Submodule.mem_inf.1 hx).1) ⟨k, hkQ, hΦk⟩`. Conclude with `⟨w, (Submodule.mem_inf.1 hw).1, hw0, hfix⟩`.
-/
theorem C_gen (M : ι → Module.End ℂ U) (hc : ∀ i j, Commute (M i) (M j)) (Φ : U →ₗ[ℂ] ℂ) :
    ∀ (n : ℕ) (P : Submodule ℂ U), Module.finrank ℂ P = n → (∀ i, ∀ v ∈ P, M i v ∈ P) →
      (∀ i, ∀ v ∈ P, Φ (M i v) = Φ v) → (∃ v ∈ P, Φ v ≠ 0) → ∃ w ∈ P, w ≠ 0 ∧ ∀ i, M i w = w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hst hinv hv
  obtain ⟨v, hv, hΦv⟩ := hv
  by_cases hnil : ∀ i, ∀ u ∈ P, ∃ k : ℕ, ((M i - 1) ^ k) u = 0
  · refine C_nil M hc _ P rfl ?_ hst hnil
    rintro rfl
    rw [Submodule.mem_bot] at hv
    exact hΦv (by rw [hv, map_zero])
  push Not at hnil
  obtain ⟨i, u, hu, hku⟩ := hnil
  have hgP : ∀ x ∈ P, (M i - 1) x ∈ P := C_sub_one_mem (hst i)
  obtain ⟨m, hm, hm1⟩ := ((LinearMap.eventually_isCompl_ker_pow_range_pow ((M i - 1).restrict hgP)).and
    (Filter.eventually_ge_atTop 1)).exists
  set Q : Submodule ℂ U := P ⊓ LinearMap.ker ((M i - 1) ^ m) with hQdef
  obtain ⟨k, hk, r, hr, hkr⟩ := Submodule.mem_sup.1 (hm.sup_eq_top ▸ Submodule.mem_top (x := (⟨v, hv⟩ : P)))
  have hΦr : Φ (r : U) = 0 := by
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hr
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le hm1
    rw [← hy, C_restrict_pow hgP, add_comm, pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_sub, hinv i _ (C_pow_mem hgP m' _ y.2), sub_self]
  have hkv : (k : U) + r = v := congrArg Subtype.val hkr
  have hΦk : Φ (k : U) ≠ 0 := by
    intro h0; apply hΦv; rw [← hkv, map_add, h0, hΦr, add_zero]
  have hkQ : (k : U) ∈ Q := by
    refine Submodule.mem_inf.2 ⟨k.2, ?_⟩
    rw [LinearMap.mem_ker, ← C_restrict_pow hgP, LinearMap.mem_ker.1 hk, Submodule.coe_zero]
  have hlt : Q < P := by
    refine lt_of_le_of_ne inf_le_left fun h => hku m ?_
    have h2 : u ∈ Q := h ▸ hu
    exact (Submodule.mem_inf.1 h2).2
  have hstQ : ∀ l, ∀ x ∈ Q, M l x ∈ Q := by
    intro l x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨hst l x hx1, ?_⟩
    rw [LinearMap.mem_ker] at hx2 ⊢
    rw [← C_comm_pow hc i l m x, hx2, map_zero]
  obtain ⟨w, hw, hw0, hfix⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt) Q rfl hstQ
    (fun l x hx => hinv l x (Submodule.mem_inf.1 hx).1) ⟨k, hkQ, hΦk⟩
  exact ⟨w, (Submodule.mem_inf.1 hw).1, hw0, hfix⟩

end Fixed

/- English proof (translation)
Establish `hv : ∃ v ∈ (⊤ : Submodule ℂ U), Φ v ≠ 0`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hΦ (LinearMap.ext fun v => by rw [h v Submodule.mem_top, LinearMap.zero_apply])`. Take `⟨w, -, hw0, hfix⟩` from `C_gen M hc Φ _ ⊤ rfl (fun _ _ _ => Submodule.mem_top) (fun i v _ => LinearMap.congr_fun (hinv i) v) hv`.

Conclude with `⟨w, hw0, hfix⟩`.
-/
theorem exists_fixed {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] {ι : Type*}
    (M : ι → Module.End ℂ U) (hc : ∀ i j, Commute (M i) (M j)) (Φ : U →ₗ[ℂ] ℂ) (hΦ : Φ ≠ 0)
    (hinv : ∀ i, Φ ∘ₗ M i = Φ) : ∃ w, w ≠ 0 ∧ ∀ i, M i w = w := by
  have hv : ∃ v ∈ (⊤ : Submodule ℂ U), Φ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hΦ (LinearMap.ext fun v => by rw [h v Submodule.mem_top, LinearMap.zero_apply])
  obtain ⟨w, -, hw0, hfix⟩ := C_gen M hc Φ _ ⊤ rfl (fun _ _ _ => Submodule.mem_top)
    (fun i v _ => LinearMap.congr_fun (hinv i) v) hv
  exact ⟨w, hw0, hfix⟩

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨y₀, hy₀⟩ : ∃ y, B w₀ y ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hne (funext h)`. Set `M : ℝ → Module.End ℂ W` to `fun t => Complex.exp (-((c + d) * t)) • (L t).restrict (hW t)`.

Establish `hMv : ∀ t (w : W), ((M t w : W) : X → ℂ) = Complex.exp (-((c + d) * t)) • L t (w : X → ℂ)` using `fun _ _ => rfl`. Set `Φ : W →ₗ[ℂ] ℂ` to `{ toFun := fun w => B (w : X → ℂ) y₀ / B w₀ y₀ map_add' := fun v w => by`. Simplify using `only [Submodule.coe_add]`. Rewrite using `[hadd _ v.2 _ w.2, Pi.add_apply, add_div]`. Use the proof step `map_smul' := fun a w => by`.

Simplify using `only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]`. Rewrite using `[hsmul a _ w.2, Pi.smul_apply, smul_eq_mul, mul_div_assoc] }`. Establish `hΦ : ∀ w : W, Φ w = B (w : X → ℂ) y₀ / B w₀ y₀` using `fun _ => rfl`. Set `P : Submodule ℂ W` to `{ carrier := {w | ∃ a : ℂ, B (w : X → ℂ) = a • B w₀} add_mem' := fun {v w} hv hw => by`. Take `⟨a, ha⟩` from `hv`.

Take `⟨b, hb⟩` from `hw`. Conclude with `⟨a + b, by simp only [Submodule.coe_add]; rw [hadd _ v.2 _ w.2, ha, hb, add_smul]⟩`. Use the proof step `zero_mem' := ⟨0, by`. Use `hsmul 0 w₀ hw₀` as an intermediate fact. Simplify using `using this⟩`.

Use the proof step `smul_mem' := fun a w hw => by`. Take `⟨b, hb⟩` from `hw`. Conclude with `⟨a * b, by simp only [Submodule.coe_smul]; rw [hsmul a _ w.2, hb, smul_smul]⟩ }`. Establish `hBM : ∀ t (w : W), B ((M t w : W) : X → ℂ) = Complex.exp (-(c * t)) • L' t (B (w : X → ℂ))`. Introduce `t w`.

Rewrite using `[hMv, hsmul _ _ (hW t _ w.2), hB t _ w.2, smul_smul, ← Complex.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hPM : ∀ t (w : W) (a : ℂ), B (w : X → ℂ) = a • B w₀ → B ((M t w : W) : X → ℂ) = a • B w₀`. Introduce `t w a ha`.

Rewrite using `[hBM, ha, map_smul, heig, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[mul_comm _ a, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]`. Establish `hc : ∀ s t, Commute (M s) (M t)`. Introduce `s t`.

Use `LinearMap.ext fun w => Subtype.ext ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply]`. Rewrite using `[hMv, hMv, hMv, hMv, map_smul, map_smul, hL s t _ w.2, smul_smul, smul_smul, mul_comm]`. Take `⟨w, -, hw0, hfix⟩` from `C_gen M hc Φ _ P rfl (fun t w hw => by obtain ⟨a, ha⟩ := hw; exact ⟨a, hPM t w a ha⟩) (fun t w hw => by obtain ⟨a, ha⟩ := hw; rw [hΦ, hΦ, hPM t w a ha, ha]) ⟨⟨w₀, hw₀⟩, ⟨1, by rw [one_smul]⟩, by rw [hΦ]; exact div_ne_zero hy₀ hy₀⟩`. Use `⟨w, w.2, fun h => hw0 (Subtype.ext h), fun t => ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrArg Subtype.val (hfix t)`. Rewrite `h1` using `[hMv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]`. Use `_ = Complex.exp ((c + d) * t) • (w : X → ℂ) := by rw [h1]`.
-/
theorem eig_lift {X Y : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W]
    (L : ℝ → (X → ℂ) →ₗ[ℂ] (X → ℂ)) (hL : ∀ s t, ∀ w ∈ W, L s (L t w) = L t (L s w))
    (hW : ∀ t, ∀ w ∈ W, L t w ∈ W) (L' : ℝ → (Y → ℂ) →ₗ[ℂ] (Y → ℂ)) (B : (X → ℂ) → (Y → ℂ))
    (hadd : ∀ v ∈ W, ∀ w ∈ W, B (v + w) = B v + B w) (hsmul : ∀ (a : ℂ), ∀ w ∈ W, B (a • w) = a • B w)
    (c d : ℂ) (hB : ∀ t : ℝ, ∀ w ∈ W, B (L t w) = Complex.exp (d * t) • L' t (B w))
    (w₀ : X → ℂ) (hw₀ : w₀ ∈ W) (hne : B w₀ ≠ 0) (heig : ∀ t : ℝ, L' t (B w₀) = Complex.exp (c * t) • B w₀) :
    ∃ F ∈ W, F ≠ 0 ∧ ∀ t : ℝ, L t F = Complex.exp ((c + d) * t) • F := by
  obtain ⟨y₀, hy₀⟩ : ∃ y, B w₀ y ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  let M : ℝ → Module.End ℂ W := fun t => Complex.exp (-((c + d) * t)) • (L t).restrict (hW t)
  have hMv : ∀ t (w : W), ((M t w : W) : X → ℂ) = Complex.exp (-((c + d) * t)) • L t (w : X → ℂ) := fun _ _ => rfl
  let Φ : W →ₗ[ℂ] ℂ :=
    { toFun := fun w => B (w : X → ℂ) y₀ / B w₀ y₀
      map_add' := fun v w => by
        simp only [Submodule.coe_add]
        rw [hadd _ v.2 _ w.2, Pi.add_apply, add_div]
      map_smul' := fun a w => by
        simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
        rw [hsmul a _ w.2, Pi.smul_apply, smul_eq_mul, mul_div_assoc] }
  have hΦ : ∀ w : W, Φ w = B (w : X → ℂ) y₀ / B w₀ y₀ := fun _ => rfl
  let P : Submodule ℂ W :=
    { carrier := {w | ∃ a : ℂ, B (w : X → ℂ) = a • B w₀}
      add_mem' := fun {v w} hv hw => by
        obtain ⟨a, ha⟩ := hv; obtain ⟨b, hb⟩ := hw
        exact ⟨a + b, by simp only [Submodule.coe_add]; rw [hadd _ v.2 _ w.2, ha, hb, add_smul]⟩
      zero_mem' := ⟨0, by
        have := hsmul 0 w₀ hw₀
        simpa using this⟩
      smul_mem' := fun a w hw => by
        obtain ⟨b, hb⟩ := hw
        exact ⟨a * b, by simp only [Submodule.coe_smul]; rw [hsmul a _ w.2, hb, smul_smul]⟩ }
  have hBM : ∀ t (w : W), B ((M t w : W) : X → ℂ) = Complex.exp (-(c * t)) • L' t (B (w : X → ℂ)) := by
    intro t w
    rw [hMv, hsmul _ _ (hW t _ w.2), hB t _ w.2, smul_smul, ← Complex.exp_add]
    congr 2
    ring
  have hPM : ∀ t (w : W) (a : ℂ), B (w : X → ℂ) = a • B w₀ → B ((M t w : W) : X → ℂ) = a • B w₀ := by
    intro t w a ha
    rw [hBM, ha, map_smul, heig, smul_smul, smul_smul]
    congr 1
    rw [mul_comm _ a, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hc : ∀ s t, Commute (M s) (M t) := by
    intro s t
    refine LinearMap.ext fun w => Subtype.ext ?_
    simp only [Module.End.mul_apply]
    rw [hMv, hMv, hMv, hMv, map_smul, map_smul, hL s t _ w.2, smul_smul, smul_smul, mul_comm]
  obtain ⟨w, -, hw0, hfix⟩ := C_gen M hc Φ _ P rfl
    (fun t w hw => by obtain ⟨a, ha⟩ := hw; exact ⟨a, hPM t w a ha⟩)
    (fun t w hw => by obtain ⟨a, ha⟩ := hw; rw [hΦ, hΦ, hPM t w a ha, ha])
    ⟨⟨w₀, hw₀⟩, ⟨1, by rw [one_smul]⟩, by rw [hΦ]; exact div_ne_zero hy₀ hy₀⟩
  refine ⟨w, w.2, fun h => hw0 (Subtype.ext h), fun t => ?_⟩
  have h1 := congrArg Subtype.val (hfix t)
  rw [hMv] at h1
  calc L t (w : X → ℂ) = Complex.exp ((c + d) * t) • (Complex.exp (-((c + d) * t)) • L t (w : X → ℂ)) := by
        rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
    _ = Complex.exp ((c + d) * t) • (w : X → ℂ) := by rw [h1]

end PositivityTheory.Rg.Rs.SliceClasses

end
