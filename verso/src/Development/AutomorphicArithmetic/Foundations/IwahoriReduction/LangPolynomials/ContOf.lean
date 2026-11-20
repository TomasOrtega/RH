import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PConj
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FrobEx

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

/- English proof (translation)
Unfold `Cg at *`. Use `hc.trans ?_` and prove the remaining obligations. Rewrite using `[norm_pow, norm_pow]`. Conclude with `pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) h`.
-/
private theorem cg_mono {l : ℕ} [Fact l.Prime] {n N : ℕ} (h : n ≤ N) {a b : Qbar l} (hc : Cg N a b) : Cg n a b := by
  unfold Cg at *
  refine hc.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) h

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => intro h`. Simplify using `using h`. Consider the case `succ d ih`.

Introduce `h`. Apply `ih` to reduce the goal to its premises. Introduce `x`. Establish `hsum` using `hZ.nrm (r + d) s hs x`. Unfold `Cg at h ⊢`.

Rewrite using `[sub_zero, hsum]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_` and prove the remaining obligations. Introduce `x' _`. Use `h x'` as an intermediate fact. Rewrite `this` using `[sub_zero]`.

Conclude with `this`.
-/
private theorem cg_down {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {A : ValuationSubring Ω}
    {Z : Sy Ω l} (hZ : IwI c A Z) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (n r : ℕ) :
    ∀ d, (∀ x, Cg n (Z (r + d) s x) 0) → ∀ x, Cg n (Z r s x) 0 := by
  intro d
  induction d with
  | zero => intro h; simpa using h
  | succ d ih =>
    intro h
    apply ih
    intro x
    have hsum := hZ.nrm (r + d) s hs x
    unfold Cg at h ⊢
    rw [sub_zero, hsum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
    intro x' _
    have := h x'
    rw [sub_zero] at this
    exact this

/- English proof (translation)
Use `haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Use `haveI : Fact (1 < l ^ m) := ⟨Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt⟩`. Establish `hsurj : Function.Surjective (PadicInt.toZModPow (p` using `l) m) := by`. Introduce `y`. Take `⟨k, rfl⟩` from `ZMod.natCast_zmod_surjective y`.

Conclude with `⟨k, map_natCast _ k⟩`. Take `⟨u, hu⟩` from `IsLocalRing.surjective_units_map_of_local_ringHom _ hsurj hsurj.isLocalHom x`. Conclude with `⟨u, congrArg Units.val hu⟩`.
-/
private theorem unit_lift (l : ℕ) [Fact l.Prime] (m : ℕ) (hm : 1 ≤ m) (x : (ZMod (l ^ m))ˣ) :
    ∃ u : ℤ_[l]ˣ, PadicInt.toZModPow m (u : ℤ_[l]) = x := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Fact (1 < l ^ m) := ⟨Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt⟩
  have hsurj : Function.Surjective (PadicInt.toZModPow (p := l) m) := by
    intro y
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective y
    exact ⟨k, map_natCast _ k⟩
  obtain ⟨u, hu⟩ := IsLocalRing.surjective_units_map_of_local_ringHom _ hsurj hsurj.isLocalHom x
  exact ⟨u, congrArg Units.val hu⟩

/- English proof (translation)
Unfold `UpperTheory.Kd.C7.SContOf`. Introduce `l _ hl2 Ω _ _ _ A hA c β ζ hζ Z hZ hP`. Take `⟨c₀, m₀, hP⟩` from `hP`. Introduce `r n`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`.

Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Use `set m := r + (m₀ + n + c₀ + 1) with hm_def`. Establish `hm0 : m₀ ≤ m` using `by omega`. Take `⟨P, hKP⟩` from `hP m hm0`. Use `set N := m - c₀ with hN`.

Take `⟨hprim, hNm, hu, ho, hk⟩` from `hKP`. Establish `hlN : 0 < l ^ N` using `pow_pos (Fact.out : l.Prime).pos N`. Use `choose w hw using fun i : Fin β.d => IsAlgClosed.exists_pow_nat_eq (pv (P i) (ζ m)) hlN`. Establish `hfe` using `UpperTheory.Kd.C7.pFrobEx l hl2 Ω A hA`. Use `haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`.

Establish `hlift : ∀ y : (ZMod (l ^ m))ˣ, ∃ t ∈ Ine (F` using `ℚ) A, cycMod ℚ Ω l m t = y⁻¹ := by`. Introduce `y`. Take `⟨u, hu'⟩` from `unit_lift l m (by omega) y⁻¹`. Take `⟨t, ht, htu⟩` from `hfe.2.2 u`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations.

Use `ext`. Simplify using `[ReciprocityTheory.Gal.cycMod, htu, hu']`. Use `choose tt htt hcyc using hlift`. Set `f : (ZMod (l ^ m))ˣ × Option (Fin β.d) → Ω` to `fun q => (tt q.1)⁻¹ (q.2.elim (ζ N) w)`. Set `E` to `IntermediateField.adjoin ℚ (Set.range f)`.

Use `haveI : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)`. Use `⟨(cycMod ℚ Ω l m).ker ⊓ E.fixingSubgroup, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_inf]`. Use `IsOpen.inter ?_ E.fixingSubgroup_isOpen` and prove the remaining obligations. Use `(GlobalTheory.KZ.IwC.isLocallyConstant_cycMod (Ω := Ω) (l := l) m).isOpen_fiber 1` as an intermediate fact.

Rewrite using `[MonoidHom.coe_ker]`. Conclude with `this`. Introduce `s hsU hs`. Take `⟨hsk, hsE⟩` from `Subgroup.mem_inf.mp hsU`. Establish `hfix : ∀ q, s (f q) = f q`.

Introduce `q`. Conclude with `(mem_fixingSubgroup_iff _).mp hsE (f q) (IntermediateField.subset_adjoin ℚ _ ⟨q, rfl⟩)`. Apply `cg_down hZ hs n r (m₀ + n + c₀ + 1)` to reduce the goal to its premises. Introduce `y`. Establish `hsH : s ∈ Hm l A m`.

Unfold `UpperTheory.Kd.C7.Hm`. Conclude with `Subgroup.mem_inf.mpr ⟨hs, hsk⟩`. Take `⟨hconjH, hconj⟩` from `UpperTheory.Kd.C7.pConj l hl2 Ω A hA c Z hZ m s hsH (tt y) (htt y)`. Establish `hZeq : Z m (tt y * s * (tt y)⁻¹) 1 = Z m s y`. Rewrite using `[hconj]`.

Simplify using `[hcyc]`. Establish `hconjH'` using `hconjH`. Unfold `UpperTheory.Kd.C7.Hm at hconjH'`. Establish `hs'I` using `(Subgroup.mem_inf.mp hconjH').1`. Establish `hs'k : cycMod ℚ Ω l m (tt y * s * (tt y)⁻¹) = 1` using `(Subgroup.mem_inf.mp hconjH').2`.

Establish `hs'fix : ∀ o : Option (Fin β.d), (tt y * s * (tt y)⁻¹) (o.elim (ζ N) w) = o.elim (ζ N) w`. Introduce `o`. Establish `h` using `hfix (y, o)`. Rewrite using `[AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]`. Establish `hz : (tt y * s * (tt y)⁻¹) (ζ N) = ζ N` using `hs'fix none`.

Take `⟨k, hkv, hcg⟩` from `hk _ hs'I hs'k hz`. Establish `hk0 : ∀ i, k i = 0`. Introduce `i`. Establish `hwi : (tt y * s * (tt y)⁻¹) (w i) = w i` using `hs'fix (some i)`. Establish `h0 : KumVal N (ζ N) (pv (P i) (ζ m)) (tt y * s * (tt y)⁻¹) 0` using `⟨w i, hw i, by rw [hwi]; simp⟩`.

Conclude with `kumVal_unique hprim hz (hu i).2.1 (hkv i) h0`. Rewrite using `[← hZeq]`. Apply `cg_mono (n := n) (N := N) (by omega)` to reduce the goal to its premises. Simplify `hcg` using `[hk0]`.
-/
theorem UpperTheory.Kd.C7.pContOf :
    UpperTheory.Kd.C7.SContOf := by
  unfold UpperTheory.Kd.C7.SContOf
  intro l _ hl2 Ω _ _ _ A hA c β ζ hζ Z hZ hP
  obtain ⟨c₀, m₀, hP⟩ := hP
  intro r n
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  set m := r + (m₀ + n + c₀ + 1) with hm_def
  have hm0 : m₀ ≤ m := by omega
  obtain ⟨P, hKP⟩ := hP m hm0
  set N := m - c₀ with hN
  obtain ⟨hprim, hNm, hu, ho, hk⟩ := hKP
  have hlN : 0 < l ^ N := pow_pos (Fact.out : l.Prime).pos N
  choose w hw using fun i : Fin β.d => IsAlgClosed.exists_pow_nat_eq (pv (P i) (ζ m)) hlN
  have hfe := UpperTheory.Kd.C7.pFrobEx l hl2 Ω A hA
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hlift : ∀ y : (ZMod (l ^ m))ˣ, ∃ t ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m t = y⁻¹ := by
    intro y
    obtain ⟨u, hu'⟩ := unit_lift l m (by omega) y⁻¹
    obtain ⟨t, ht, htu⟩ := hfe.2.2 u
    refine ⟨t, ht, ?_⟩
    ext
    simp [ReciprocityTheory.Gal.cycMod, htu, hu']
  choose tt htt hcyc using hlift
  let f : (ZMod (l ^ m))ˣ × Option (Fin β.d) → Ω := fun q => (tt q.1)⁻¹ (q.2.elim (ζ N) w)
  let E := IntermediateField.adjoin ℚ (Set.range f)
  haveI : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)
  refine ⟨(cycMod ℚ Ω l m).ker ⊓ E.fixingSubgroup, ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    refine IsOpen.inter ?_ E.fixingSubgroup_isOpen
    have := (GlobalTheory.KZ.IwC.isLocallyConstant_cycMod (Ω := Ω) (l := l) m).isOpen_fiber 1
    rw [MonoidHom.coe_ker]
    exact this
  · intro s hsU hs
    obtain ⟨hsk, hsE⟩ := Subgroup.mem_inf.mp hsU
    have hfix : ∀ q, s (f q) = f q := by
      intro q
      exact (mem_fixingSubgroup_iff _).mp hsE (f q) (IntermediateField.subset_adjoin ℚ _ ⟨q, rfl⟩)
    apply cg_down hZ hs n r (m₀ + n + c₀ + 1)
    intro y
    have hsH : s ∈ Hm l A m := by
      unfold UpperTheory.Kd.C7.Hm
      exact Subgroup.mem_inf.mpr ⟨hs, hsk⟩
    obtain ⟨hconjH, hconj⟩ := UpperTheory.Kd.C7.pConj l hl2 Ω A hA c Z hZ m s hsH (tt y) (htt y)
    have hZeq : Z m (tt y * s * (tt y)⁻¹) 1 = Z m s y := by
      rw [hconj]
      simp [hcyc]
    have hconjH' := hconjH
    unfold UpperTheory.Kd.C7.Hm at hconjH'
    have hs'I := (Subgroup.mem_inf.mp hconjH').1
    have hs'k : cycMod ℚ Ω l m (tt y * s * (tt y)⁻¹) = 1 := (Subgroup.mem_inf.mp hconjH').2
    have hs'fix : ∀ o : Option (Fin β.d),
        (tt y * s * (tt y)⁻¹) (o.elim (ζ N) w) = o.elim (ζ N) w := by
      intro o
      have h := hfix (y, o)
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, ← AlgEquiv.mul_apply, mul_inv_cancel,
        AlgEquiv.one_apply]
    have hz : (tt y * s * (tt y)⁻¹) (ζ N) = ζ N := hs'fix none
    obtain ⟨k, hkv, hcg⟩ := hk _ hs'I hs'k hz
    have hk0 : ∀ i, k i = 0 := by
      intro i
      have hwi : (tt y * s * (tt y)⁻¹) (w i) = w i := hs'fix (some i)
      have h0 : KumVal N (ζ N) (pv (P i) (ζ m)) (tt y * s * (tt y)⁻¹) 0 :=
        ⟨w i, hw i, by rw [hwi]; simp⟩
      exact kumVal_unique hprim hz (hu i).2.1 (hkv i) h0
    rw [← hZeq]
    apply cg_mono (n := n) (N := N) (by omega)
    simpa [hk0] using hcg
