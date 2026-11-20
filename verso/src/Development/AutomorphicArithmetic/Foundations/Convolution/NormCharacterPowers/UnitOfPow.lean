import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.SumSatUnit
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

open UpperTheory.ConvolutionTheory.R
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Published PositivityTheory.RgJS

section

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
The claim follows from `MonoidHom.pow_apply χ.1 j _`.
-/
private theorem val_pow' (χ : HChar E) (j : ℕ) (w : HeightOneSpectrum (𝓞 E)) : (χ ^ j).val w = χ.val w ^ j :=
  MonoidHom.pow_apply χ.1 j _

/- English proof (translation)
Introduce `x hx`. Establish `e : (χ ^ j).loc w x = χ.loc w x ^ j` using `MonoidHom.pow_apply χ.1 j _`. Rewrite using `[e, h x hx, one_pow]`.
-/
private theorem unr_pow {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) (j : ℕ) : (χ ^ j).UnrAt w := by
  intro x hx
  have e : (χ ^ j).loc w x = χ.loc w x ^ j := MonoidHom.pow_apply χ.1 j _
  rw [e, h x hx, one_pow]

/- English proof (translation)
Introduce `x hx`. Establish `e : (χ⁻¹).loc w x = (χ.loc w x)⁻¹` using `rfl`. Rewrite using `[e, h x hx, inv_one]`.
-/
private theorem unr_inv {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) : (χ⁻¹).UnrAt w := by
  intro x hx
  have e : (χ⁻¹).loc w x = (χ.loc w x)⁻¹ := rfl
  rw [e, h x hx, inv_one]

/- English proof (translation)
Introduce `x`. Establish `e : χ.1 x ^ l = 1`. Establish `e1 : (χ ^ l).1 x = χ.1 x ^ l` using `MonoidHom.pow_apply χ.1 l _`. Rewrite using `[← e1, h]`. Both sides reduce to the same expression.

Establish `e2 : ((χ.1 x : ℂˣ) : ℂ) ^ l = 1` using `by rw [← Units.val_pow_eq_pow_val, e, Units.val_one]`. Conclude with `Complex.norm_eq_one_of_pow_eq_one e2 hl`.
-/
private theorem unit_of_pow {χ : HChar E} {l : ℕ} (hl : l ≠ 0) (h : χ ^ l = 1) : χ.IsUnitary := by
  intro x
  have e : χ.1 x ^ l = 1 := by
    have e1 : (χ ^ l).1 x = χ.1 x ^ l := MonoidHom.pow_apply χ.1 l _
    rw [← e1, h]; rfl
  have e2 : ((χ.1 x : ℂˣ) : ℂ) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, e, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one e2 hl

variable [IsTotallyComplex E]

/- English proof (translation)
Take `⟨ω, hω, hc⟩` from `h`. Use `⟨_, fun x => ?_, hc.twist χ⟩` and prove the remaining obligations. Establish `e : (ω * χ ^ n).1 x = ω.1 x * χ.1 x ^ n` using `congrArg (ω.1 x * ·) (MonoidHom.pow_apply χ.1 n _)`. Rewrite using `[e, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hω x, hχ x, one_pow, one_mul]`.
-/
private theorem unit_twist {n : ℕ} {π : CG E n} (h : π.IsUnitary) {χ : HChar E} (hχ : χ.IsUnitary) :
    (π.twist χ).IsUnitary := by
  obtain ⟨ω, hω, hc⟩ := h
  refine ⟨_, fun x => ?_, hc.twist χ⟩
  have e : (ω * χ ^ n).1 x = ω.1 x * χ.1 x ^ n := congrArg (ω.1 x * ·) (MonoidHom.pow_apply χ.1 n _)
  rw [e, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hω x, hχ x, one_pow, one_mul]

/- English proof (translation)
Take `⟨B, hB⟩` from `h`. Use `satake_twist_holds E n _ χ⁻¹ w B (unr_inv hχ) hB` as an intermediate fact. Rewrite `this` using `[← CG.twist_mul, mul_inv_cancel, CG.twist_one]`. Conclude with `⟨_, this⟩`.
-/
private theorem sat_untw {n : ℕ} {π : CG E n} {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w)
    (h : ∃ B, (π.twist χ).HasSat w B) : ∃ B, π.HasSat w B := by
  obtain ⟨B, hB⟩ := h
  have := satake_twist_holds E n _ χ⁻¹ w B (unr_inv hχ) hB
  rw [← CG.twist_mul, mul_inv_cancel, CG.twist_one] at this
  exact ⟨_, this⟩

/- English proof (translation)
Rewrite using `[hB.unique (satake_twist_holds E n π χ w _ hχ hα), Multiset.map_map, Multiset.map_map]`. Conclude with `Multiset.map_congr rfl fun a _ => by simp`.
-/
private theorem sat_key {n : ℕ} {π : CG E n} {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w)
    {α : Fin n → ℂˣ} (hα : π.HasSat w (Finset.univ.val.map α)) {B : Multiset ℂˣ} (hB : (π.twist χ).HasSat w B) :
    B.map (fun u : ℂˣ => (u : ℂ)) = Finset.univ.val.map fun a => (α a : ℂ) * (χ.val w : ℂ) := by
  rw [hB.unique (satake_twist_holds E n π χ w _ hχ hα), Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun a _ => by simp

end

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `h'` using `Filter.eventually_cofinite.1 h`. Establish `h2` using `(h'.image fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)).eventually_cofinite_notMem`. Use `filter_upwards [h2, S.eventually_cofinite_notMem] with v hv hvS`. Take `⟨w, hw⟩` from `hs ⟨v, hvS⟩`.

Establish `e : w.1.under (𝓞 K) = v` using `(hu w).symm.trans (congrArg Subtype.val hw)`. Assume the negation of the conclusion as `hc`. Use `hv ⟨w.1, fun hg => hc ?_, e⟩` and prove the remaining obligations. Take `⟨B, hB, -⟩` from `hg (f w) (by rw [← hu w]; exact hf w)`. Conclude with `⟨B, e ▸ hB⟩`.

Use `filter_upwards [h, T.eventually_cofinite_notMem] with w hw hwT`. Take `⟨B, -, hB⟩` from `hw (f ⟨w, hwT⟩) (by have := hf ⟨w, hwT⟩; rwa [hu] at this)`. Conclude with `⟨_, hB⟩`.
-/
private theorem ev_sat {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    {S : Finset (HeightOneSpectrum (𝓞 K))} {T : Finset (HeightOneSpectrum (𝓞 M))} {u : Off M T → Off K S}
    {f : Off M T → ℕ} (hu : ∀ w, (u w).1 = w.1.under (𝓞 K)) (hf : ∀ w, normV w.1 = normV (u w).1 ^ f w)
    (hs : Function.Surjective u) {sat : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop}
    {satE : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop} (h : WeakBC sat satE) :
    (∀ᶠ v in Filter.cofinite, ∃ B, sat v B) ∧ ∀ᶠ w in Filter.cofinite, ∃ B, satE w B := by
  constructor
  · have h' := Filter.eventually_cofinite.1 h
    have h2 := (h'.image fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)).eventually_cofinite_notMem
    filter_upwards [h2, S.eventually_cofinite_notMem] with v hv hvS
    obtain ⟨w, hw⟩ := hs ⟨v, hvS⟩
    have e : w.1.under (𝓞 K) = v := (hu w).symm.trans (congrArg Subtype.val hw)
    by_contra hc
    refine hv ⟨w.1, fun hg => hc ?_, e⟩
    obtain ⟨B, hB, -⟩ := hg (f w) (by rw [← hu w]; exact hf w)
    exact ⟨B, e ▸ hB⟩
  · filter_upwards [h, T.eventually_cofinite_notMem] with w hw hwT
    obtain ⟨B, -, hB⟩ := hw (f ⟨w, hwT⟩) (by have := hf ⟨w, hwT⟩; rwa [hu] at this)
    exact ⟨_, hB⟩

/- English proof (translation)
Take `⟨B, hB, B', hB', e⟩` from `h`. Establish `e1` using `sat_key (hν.1 v) hα hB`. Establish `e2` using `fun i => sat_key ((hν' i).1 w) (hβ i) (hB' i)`. Simplify using `only [(hν' _).2.1 w] at e2`. Rewrite `e1` using `[hν.2.1 v]`.

Establish `e3` using `congrArg (Multiset.map fun u : ℂˣ => (u : ℂ)) e`. Establish `e4 : Multiset.map (fun u : ℂˣ => (u : ℂ)) (∑ i, B' i) = ∑ i, Multiset.map (fun u : ℂˣ => (u : ℂ)) (B' i)` using `map_sum (Multiset.mapAddMonoidHom fun u : ℂˣ => (u : ℂ)) B' Finset.univ`. Establish `e5` using `congrArg (Multiset.map fun c : ℂ => c ^ f) e1`. Rewrite `e5` using `[Multiset.map_map, Multiset.map_map]`. Rewrite `e3` using `[e4, Multiset.map_map]`.

Simplify using `only [e2] at e3`. Rewrite using `[← e3]`. Conclude with `Eq.trans (Multiset.map_congr rfl fun a _ => by simp) e5`.
-/
private theorem lift_eq {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsTotallyComplex K] [IsTotallyComplex M] {n : ℕ} {π : CG K n} {ν : HChar K} {t : ℝ} (hν : ν.IsAbsPow t)
    {ι : Type} [Fintype ι] {m : ι → ℕ} {P : ∀ i, CG M (m i)} {ν' : ι → HChar M} {s : ι → ℝ}
    (hν' : ∀ i, (ν' i).IsAbsPow (s i)) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} {f : ℕ}
    {α : Fin n → ℂˣ} (hα : π.HasSat v (Finset.univ.val.map α)) {β : ∀ i, Fin (m i) → ℂˣ}
    (hβ : ∀ i, (P i).HasSat w (Finset.univ.val.map (β i)))
    (h : ∃ B, (π.twist ν).HasSat v B ∧ sumSat (fun i => (P i).twist (ν' i)) w (B.map (· ^ f))) :
    ∑ i, Finset.univ.val.map (fun a => (β i a : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(s i : ℂ))) =
      Finset.univ.val.map fun a => ((α a : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(t : ℂ))) ^ f := by
  obtain ⟨B, hB, B', hB', e⟩ := h
  have e1 := sat_key (hν.1 v) hα hB
  have e2 := fun i => sat_key ((hν' i).1 w) (hβ i) (hB' i)
  simp only [(hν' _).2.1 w] at e2
  rw [hν.2.1 v] at e1
  have e3 := congrArg (Multiset.map fun u : ℂˣ => (u : ℂ)) e
  have e4 : Multiset.map (fun u : ℂˣ => (u : ℂ)) (∑ i, B' i) = ∑ i, Multiset.map (fun u : ℂˣ => (u : ℂ)) (B' i) :=
    map_sum (Multiset.mapAddMonoidHom fun u : ℂˣ => (u : ℂ)) B' Finset.univ
  have e5 := congrArg (Multiset.map fun c : ℂ => c ^ f) e1
  rw [Multiset.map_map, Multiset.map_map] at e5
  rw [e4, Multiset.map_map] at e3
  simp only [e2] at e3
  rw [← e3]
  exact Eq.trans (Multiset.map_congr rfl fun a _ => by simp) e5

/- English proof (translation)
Introduce `hA hS hC K M _ _ _ _ _ _ _ _ hl η hη n π π₁ ι _ m P hn hm hπ hπ₁`. Take `⟨ν, hν, hU⟩` from `unit_exponent_holds K`. Take `⟨ν', hν', hU'⟩` from `unit_exponent_holds M`. Take `⟨π0, t, hu0, rfl⟩` from `hU n π hn`. Take `⟨π1, t1, hu1, rfl⟩` from `hU n π₁ hn`.

Use `choose P0 s huP hP using fun i => hU' (m i) (P i) (hm i)`. Take `rfl : P = fun i => (P0 i).twist (ν' (s i))` from `funext hP`. Establish `hηl : η ^ Module.finrank K M = 1` using `hη.1.2.1`. Establish `hηu : ∀ j : ℕ, (η ^ j).IsUnitary` using `fun j => unit_of_pow hl.ne_zero (by rw [← pow_mul, mul_comm, pow_mul, hηl, one_pow])`. Take `⟨S1, T1, u1, f1, -, -, hu1', hunr1, hf1, hc1⟩` from `hC K M hl η hη ∅ ∅`.

Establish `hs1 : Function.Surjective u1` using `fun v => by`. Establish `: Nat.card {w // u1 w = v} ≠ 0`. Break down `hc1.fib v with h | h` into its components or cases. Rewrite using `[h.1]`. Conclude with `hl.ne_zero`.

Rewrite using `[h.1]`. Conclude with `one_ne_zero`. Take `⟨⟨w, hw⟩⟩` from `(Nat.card_ne_zero.1 this).1`. Conclude with `⟨w, hw⟩`. Take `⟨e0, eP⟩` from `ev_sat hu1' hf1 hs1 hπ`.

Take `⟨e1, -⟩` from `ev_sat hu1' hf1 hs1 hπ₁`. Set `X : Set (Σ a, CG K a)` to `insert ⟨n, π1⟩ (Set.range fun j : ℕ => ⟨n, π0.twist (η ^ j)⟩)`. Set `X' : Set (Σ a, CG M a)` to `Set.range fun i => ⟨m i, P0 i⟩`. Establish `hXf : X.Finite`. Use `Set.Finite.insert _ (((Set.finite_lt_nat (Module.finrank K M)).image fun j : ℕ => (⟨n, π0.twist (η ^ j)⟩ : Σ a, CG K a)).subset ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨j % Module.finrank K M, Nat.mod_lt _ hl.pos, by beta_reduce; rw [← pow_eq_pow_mod j hηl]⟩`. Take `⟨S0, hS0⟩` from `hS K X hXf (by`. Introduce and unpack `_ (rfl | ⟨j, rfl⟩)`. Conclude with `⟨hn, hu1, e1.mono fun v hv => sat_untw ((hν _).1 v) hv⟩`.

Use `⟨hn, unit_twist hu0 (hηu j), ?_⟩ filter_upwards [e0, S1.eventually_cofinite_notMem] with v hv hvS` and prove the remaining obligations. Take `⟨B, hB⟩` from `sat_untw ((hν _).1 v) hv`. Conclude with `⟨_, satake_twist_holds K n π0 _ v B (unr_pow (hunr1 ⟨v, hvS⟩) j) hB⟩)`. Take `⟨T0, hT0⟩` from `hS M X' (Set.finite_range _) (by`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `⟨hm i, huP i, eP.mono fun w ⟨B, B', hB', _⟩ => sat_untw ((hν' _).1 w) ⟨_, hB' i⟩⟩)`. Establish `hbad` using `Filter.eventually_cofinite.1 (hπ.and hπ₁)`. Take `⟨S, T, u, f, hS0S, hT0T, hu, hunr, hf, hc⟩` from `hC K M hl η hη S0 (T0 ∪ hbad.toFinset)`. Take `⟨α, hα, hsys⟩` from `hS0 S hS0S`. Take `⟨β, hβ, hsys'⟩` from `hT0 T (Finset.subset_union_left.trans hT0T)`.

Establish `hgood : ∀ w : Off M T, (∃ B, (π0.twist (ν t)).HasSat (u w).1 B ∧ sumSat (fun i => (P0 i).twist (ν' (s i))) w.1 (B.map (· ^ f w))) ∧ ∃ B, (π1.twist (ν t1)).HasSat (u w).1 B ∧ sumSat (fun i => (P0 i).twist (ν' (s i))) w.1 (B.map (· ^ f w))` using `fun w => by`. Establish `h1` using `hf w`. Rewrite `h1`, the goal using `[hu]`. Establish `h2 : w.1 ∉ hbad.toFinset` using `fun h => w.2 (hT0T (Finset.mem_union_right _ h))`. Rewrite `h2` using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not]`.

Conclude with `⟨h2.1 _ h1, h2.2 _ h1⟩`. Set `x : X` to `⟨⟨n, π1⟩, Or.inl rfl⟩`. Set `y : ℕ → X` to `fun j => ⟨⟨n, π0.twist (η ^ j)⟩, Or.inr ⟨j, rfl⟩⟩`. Set `z : ι → X' × ℝ` to `fun i => (⟨⟨m i, P0 i⟩, i, rfl⟩, s i)`. Establish `hy0 : ∀ v : Off K S, π0.HasSat v.1 (Finset.univ.val.map (α (y 0) v))` using `fun v => by`.

Establish `: (π0.twist (η ^ 0)).HasSat v.1 (Finset.univ.val.map (α (y 0) v))` using `hα (y 0) v`. Rewrite `this` using `[pow_zero, CG.twist_one]`. Then use the resulting hypothesis. Take `⟨ht, hs, hcount⟩` from `hA _ _ _ nq nq u f _ hl.pos hc X X' _ _ _ _ hsys hsys' ι x y z t1 t (fun j v => by`. Use `sat_key (unr_pow (hunr v) j) (hy0 v) (hα (y j) v)` as an intermediate fact. Rewrite `this` using `[Multiset.map_map, val_pow', Units.val_pow_eq_pow_val]`.

Rewrite using `[Multiset.map_map]`. Conclude with `this)`. Use the proof step `(fun w => lift_eq (hν t1) (fun i => hν' (s i)) (hα x (u w)) (fun i => hβ (z i).1 w) (hgood w).2)`. Use the proof step `(fun w => lift_eq (hν t) (fun i => hν' (s i)) (hy0 (u w)) (fun i => hβ (z i).1 w) (hgood w).1)`. Substitute `ht` using the available equality.

Establish `hs' : ∀ i, s i = t1` using `hs`. Establish `key : ∀ {a b : ℕ} (σ : CG M a) (σ' : CG M b) (χ : HChar M), (⟨a, σ.twist χ⟩ : Σ a, CG M a) = ⟨b, σ'.twist χ⟩ ↔ (⟨a, σ⟩ : Σ a, CG M a) = ⟨b, σ'⟩`. Introduce `a b σ σ' χ`. Prove the components needed by the constructor for the conclusion. Introduce `e`.

Take `rfl : a = b` from `(Sigma.mk.inj e).1`. Conclude with `congrArg _ (CG.twist_injective χ (eq_of_heq (Sigma.mk.inj e).2))`. Introduce `e`. Take `rfl : a = b` from `(Sigma.mk.inj e).1`. Rewrite using `[eq_of_heq (Sigma.mk.inj e).2]`.

Use `Eq.trans (congrArg Finset.card (Finset.ext fun j => ?_)) (hcount.trans (congrArg Finset.card (Finset.ext fun p => ?_)))` and prove the remaining obligations. Simplify using `only [Finset.mem_filter]`. Use `and_congr_right fun _ => ?_` and prove the remaining obligations. Rewrite using `[← CG.twist_mul, mul_comm, CG.twist_mul, Subtype.ext_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `e`. Conclude with `congrArg (Sigma.mk n) (CG.twist_injective _ e)`. Introduce `e`. Rewrite using `[eq_of_heq (Sigma.mk.inj e).2]`. Simplify using `only [Finset.mem_filter]`.

Use `and_congr_right fun _ => ?_` and prove the remaining obligations. Rewrite using `[Subtype.ext_iff, hs' p.1, hs' p.2, key]`.
-/
theorem UpperTheory.ConvolutionTheory.R.count :
    AbsCount → SysEx → CoverEx → Count := by
  intro hA hS hC K M _ _ _ _ _ _ _ _ hl η hη n π π₁ ι _ m P hn hm hπ hπ₁
  classical
  obtain ⟨ν, hν, hU⟩ := unit_exponent_holds K
  obtain ⟨ν', hν', hU'⟩ := unit_exponent_holds M
  obtain ⟨π0, t, hu0, rfl⟩ := hU n π hn
  obtain ⟨π1, t1, hu1, rfl⟩ := hU n π₁ hn
  choose P0 s huP hP using fun i => hU' (m i) (P i) (hm i)
  obtain rfl : P = fun i => (P0 i).twist (ν' (s i)) := funext hP
  have hηl : η ^ Module.finrank K M = 1 := hη.1.2.1
  have hηu : ∀ j : ℕ, (η ^ j).IsUnitary := fun j =>
    unit_of_pow hl.ne_zero (by rw [← pow_mul, mul_comm, pow_mul, hηl, one_pow])
  obtain ⟨S1, T1, u1, f1, -, -, hu1', hunr1, hf1, hc1⟩ := hC K M hl η hη ∅ ∅
  have hs1 : Function.Surjective u1 := fun v => by
    have : Nat.card {w // u1 w = v} ≠ 0 := by
      rcases hc1.fib v with h | h
      · rw [h.1]; exact hl.ne_zero
      · rw [h.1]; exact one_ne_zero
    obtain ⟨⟨w, hw⟩⟩ := (Nat.card_ne_zero.1 this).1
    exact ⟨w, hw⟩
  obtain ⟨e0, eP⟩ := ev_sat hu1' hf1 hs1 hπ
  obtain ⟨e1, -⟩ := ev_sat hu1' hf1 hs1 hπ₁
  let X : Set (Σ a, CG K a) := insert ⟨n, π1⟩ (Set.range fun j : ℕ => ⟨n, π0.twist (η ^ j)⟩)
  let X' : Set (Σ a, CG M a) := Set.range fun i => ⟨m i, P0 i⟩
  have hXf : X.Finite := by
    refine Set.Finite.insert _ (((Set.finite_lt_nat (Module.finrank K M)).image
      fun j : ℕ => (⟨n, π0.twist (η ^ j)⟩ : Σ a, CG K a)).subset ?_)
    rintro _ ⟨j, rfl⟩
    exact ⟨j % Module.finrank K M, Nat.mod_lt _ hl.pos, by
      beta_reduce; rw [← pow_eq_pow_mod j hηl]⟩
  obtain ⟨S0, hS0⟩ := hS K X hXf (by
    rintro _ (rfl | ⟨j, rfl⟩)
    · exact ⟨hn, hu1, e1.mono fun v hv => sat_untw ((hν _).1 v) hv⟩
    · refine ⟨hn, unit_twist hu0 (hηu j), ?_⟩
      filter_upwards [e0, S1.eventually_cofinite_notMem] with v hv hvS
      obtain ⟨B, hB⟩ := sat_untw ((hν _).1 v) hv
      exact ⟨_, satake_twist_holds K n π0 _ v B (unr_pow (hunr1 ⟨v, hvS⟩) j) hB⟩)
  obtain ⟨T0, hT0⟩ := hS M X' (Set.finite_range _) (by
    rintro _ ⟨i, rfl⟩
    exact ⟨hm i, huP i, eP.mono fun w ⟨B, B', hB', _⟩ => sat_untw ((hν' _).1 w) ⟨_, hB' i⟩⟩)
  have hbad := Filter.eventually_cofinite.1 (hπ.and hπ₁)
  obtain ⟨S, T, u, f, hS0S, hT0T, hu, hunr, hf, hc⟩ := hC K M hl η hη S0 (T0 ∪ hbad.toFinset)
  obtain ⟨α, hα, hsys⟩ := hS0 S hS0S
  obtain ⟨β, hβ, hsys'⟩ := hT0 T (Finset.subset_union_left.trans hT0T)
  have hgood : ∀ w : Off M T, (∃ B, (π0.twist (ν t)).HasSat (u w).1 B ∧
      sumSat (fun i => (P0 i).twist (ν' (s i))) w.1 (B.map (· ^ f w))) ∧ ∃ B, (π1.twist (ν t1)).HasSat (u w).1 B ∧
      sumSat (fun i => (P0 i).twist (ν' (s i))) w.1 (B.map (· ^ f w)) := fun w => by
    have h1 := hf w
    rw [hu] at h1 ⊢
    have h2 : w.1 ∉ hbad.toFinset := fun h => w.2 (hT0T (Finset.mem_union_right _ h))
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at h2
    exact ⟨h2.1 _ h1, h2.2 _ h1⟩
  let x : X := ⟨⟨n, π1⟩, Or.inl rfl⟩
  let y : ℕ → X := fun j => ⟨⟨n, π0.twist (η ^ j)⟩, Or.inr ⟨j, rfl⟩⟩
  let z : ι → X' × ℝ := fun i => (⟨⟨m i, P0 i⟩, i, rfl⟩, s i)
  have hy0 : ∀ v : Off K S, π0.HasSat v.1 (Finset.univ.val.map (α (y 0) v)) := fun v => by
    have : (π0.twist (η ^ 0)).HasSat v.1 (Finset.univ.val.map (α (y 0) v)) := hα (y 0) v
    rwa [pow_zero, CG.twist_one] at this
  obtain ⟨ht, hs, hcount⟩ := hA _ _ _ nq nq u f _ hl.pos hc X X' _ _ _ _ hsys hsys' ι x y z t1 t
    (fun j v => by
      have := sat_key (unr_pow (hunr v) j) (hy0 v) (hα (y j) v)
      rw [Multiset.map_map, val_pow', Units.val_pow_eq_pow_val] at this
      rw [Multiset.map_map]
      exact this)
    (fun w => lift_eq (hν t1) (fun i => hν' (s i)) (hα x (u w)) (fun i => hβ (z i).1 w) (hgood w).2)
    (fun w => lift_eq (hν t) (fun i => hν' (s i)) (hy0 (u w)) (fun i => hβ (z i).1 w) (hgood w).1)
  subst ht
  have hs' : ∀ i, s i = t1 := hs
  have key : ∀ {a b : ℕ} (σ : CG M a) (σ' : CG M b) (χ : HChar M),
      (⟨a, σ.twist χ⟩ : Σ a, CG M a) = ⟨b, σ'.twist χ⟩ ↔ (⟨a, σ⟩ : Σ a, CG M a) = ⟨b, σ'⟩ := by
    intro a b σ σ' χ
    constructor
    · intro e
      obtain rfl : a = b := (Sigma.mk.inj e).1
      exact congrArg _ (CG.twist_injective χ (eq_of_heq (Sigma.mk.inj e).2))
    · intro e
      obtain rfl : a = b := (Sigma.mk.inj e).1
      rw [eq_of_heq (Sigma.mk.inj e).2]
  refine Eq.trans (congrArg Finset.card (Finset.ext fun j => ?_))
    (hcount.trans (congrArg Finset.card (Finset.ext fun p => ?_)))
  · simp only [Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    rw [← CG.twist_mul, mul_comm, CG.twist_mul, Subtype.ext_iff]
    constructor
    · intro e
      exact congrArg (Sigma.mk n) (CG.twist_injective _ e)
    · intro e
      rw [eq_of_heq (Sigma.mk.inj e).2]
  · simp only [Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    rw [Subtype.ext_iff, hs' p.1, hs' p.2, key]
