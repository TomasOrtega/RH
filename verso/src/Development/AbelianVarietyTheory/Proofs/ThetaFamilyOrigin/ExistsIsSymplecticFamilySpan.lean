import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

set_option autoImplicit false

namespace GlobalTheory.LevelExist

/- English proof (translation)
Proceed by induction on `N using WellFoundedLT.induction with`. Consider the case `ind N ih`. Introduce `hN hF`. Distinguish the cases in `hbot : N = ⊥`. Use `⟨0, Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hbot, Submodule.span_eq_bot]`. Apply the tactic sequence `rintro _ ⟨i | i, rfl⟩ <;> exact i.elim0`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hbot`. Take `⟨-, e, he, -, he0⟩` from `hF x hx hx0`. Take `⟨z, hz, hz0⟩ : ∃ z ∈ N, B (t • e) z ≠ 0` from `by by_contra! h`.

Conclude with `he0 (hN _ (N.smul_mem _ he) h)`. Establish `: Nontrivial R` using `⟨_, _, hz0⟩`. Take `⟨u, hu⟩` from `(ht (B e z) (by simpa using hz0)).exists_left_inv`. Take `⟨f, hf, hd⟩ : ∃ f ∈ N, B e f = 1` from `⟨u • z, N.smul_mem _ hz, by simpa using hu⟩`. Establish `hd' : B f e = -1` using `by rw [← hB.neg_eq, hd]`.

Set `N' : Submodule R V` to `N ⊓ (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))`. Establish `hmem : ∀ y, y ∈ N' ↔ y ∈ N ∧ B e y = 0 ∧ B f y = 0` using `fun y => Iff.rfl`. Establish `hpr : ∀ y ∈ N, y - B y f • e - B e y • f ∈ N'` using `fun y hy => (hmem _).2 ⟨N.sub_mem (N.sub_mem hy (N.smul_mem _ he)) (N.smul_mem _ hf), by simp [hd, hB.self_eq_zero], by simp [← hB.neg_eq y f, hd', hB.self_eq_zero]⟩`. Establish `hdec : ∀ y ∈ N, ∃ a b : R, ∃ y' ∈ N', y = a • e + b • f + y'` using `fun y hy => ⟨B y f, B e y, _, hpr y hy, by abel⟩`. Take `⟨g, e', f', hs, hspan⟩` from `ih N' (lt_of_le_of_ne inf_le_left fun h => by`.

Use `((hmem f).1 (h ▸ hf)).2.1` as an intermediate fact. Simplify using `[hd] at this) (by`. Introduce `x hx hx0`. Use `hN x hx.1 fun y hy => ?_` and prove the remaining obligations. Take `⟨a, b, y', hy', rfl⟩` from `hdec y hy`.

Simplify using `[hx0 y' hy', hB.eq_iff.1 ((hmem x).1 hx).2.1, hB.eq_iff.1 ((hmem x).1 hx).2.2]) (by`. Introduce `x hx hx0`. Take `⟨a, y, hy, h₁, h₂⟩` from `hF x hx.1 hx0`. Establish `h₃ : t • (y - B y f • e - B e y • f) = t • y`. Establish `h₄ : t * B y f = 0`.

Simplify `(congrArg (B · f) h₁).symm` using `[hB.eq_iff.1 ((hmem x).1 hx).2.2]`. Establish `h₅ : t * B e y = 0`. Simplify `(congrArg (B e) h₁).symm` using `[((hmem x).1 hx).2.1]`. Simplify using `[smul_sub, smul_smul, h₄, h₅]`. Conclude with `⟨a, _, hpr y hy, h₃ ▸ h₁, h₃ ▸ h₂⟩)`.

Establish `he' : ∀ i, e' i ∈ N'` using `fun i => hspan ▸ Submodule.subset_span ⟨Sum.inl i, rfl⟩`. Establish `hf' : ∀ i, f' i ∈ N'` using `fun i => hspan ▸ Submodule.subset_span ⟨Sum.inr i, rfl⟩`. Use `⟨g + 1, Fin.cons e e', Fin.cons f f', ⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `i j`. Apply the tactic sequence `cases i using Fin.cases <;> cases j using Fin.cases`.

Simplify using `[hB.self_eq_zero]`. Simplify using `[((hmem _).1 (he' _)).2.1]`. Simplify using `[hB.eq_iff.1 ((hmem _).1 (he' _)).2.1]`. Simplify using `[hs.left_left]`. Introduce `i j`.

Apply the tactic sequence `cases i using Fin.cases <;> cases j using Fin.cases`. Simplify using `[hB.self_eq_zero]`. Simplify using `[((hmem _).1 (hf' _)).2.2]`. Simplify using `[hB.eq_iff.1 ((hmem _).1 (hf' _)).2.2]`. Simplify using `[hs.right_right]`.

Introduce `i`. Consider the cases of `i using Fin.cases`. Simplify using `[hd]`. Simplify using `[hs.left_right_self]`. Introduce `i j hij`.

Apply the tactic sequence `cases i using Fin.cases <;> cases j using Fin.cases`. Conclude with `absurd rfl hij`. Simplify using `[((hmem _).1 (hf' _)).2.1]`. Simplify using `[hB.eq_iff.1 ((hmem _).1 (he' _)).2.2]`. Simplify using `using hs.left_right_ne _ _ fun a => hij (congrArg _ a)`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Apply the tactic sequence `rintro _ ⟨i | i, rfl⟩ <;> cases i using Fin.cases`. Conclude with `he`. Conclude with `(he' _).1`.

Conclude with `hf`. Conclude with `(hf' _).1`. Introduce `y hy`. Take `⟨a, b, y', hy', rfl⟩` from `hdec y hy`. Use `Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)) ?_` and prove the remaining obligations.

Conclude with `Submodule.subset_span ⟨Sum.inl 0, rfl⟩`. Conclude with `Submodule.subset_span ⟨Sum.inr 0, rfl⟩`. Rewrite `hy'` using `[← hspan]`. Use `Submodule.span_mono ?_ hy'` and prove the remaining obligations. Introduce and unpack `_ ⟨i | i, rfl⟩`.

Conclude with `⟨Sum.inl i.succ, rfl⟩`. Conclude with `⟨Sum.inr i.succ, rfl⟩`.
-/
theorem exists_isSymplecticFamily_span {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] [IsArtinian R V]
    {B : LinearMap.BilinForm R V} (hB : B.IsAlt) (t : R) (ht : ∀ r, t * r ≠ 0 → IsUnit r) (N : Submodule R V) :
    (∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0) →
    (∀ x ∈ N, x ≠ 0 → ∃ a : R, ∃ y ∈ N, a • x = t • y ∧ t • y ≠ 0) →
    ∃ (g : ℕ) (e f : Fin g → V), IsSymplecticFamily B e f (fun _ => 1) ∧
      Submodule.span R (Set.range (Sum.elim e f)) = N := by
  induction N using WellFoundedLT.induction with
  | ind N ih =>
  intro hN hF
  by_cases hbot : N = ⊥
  · refine ⟨0, Fin.elim0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩, ?_⟩
    rw [hbot, Submodule.span_eq_bot]
    rintro _ ⟨i | i, rfl⟩ <;> exact i.elim0
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨-, e, he, -, he0⟩ := hF x hx hx0
  obtain ⟨z, hz, hz0⟩ : ∃ z ∈ N, B (t • e) z ≠ 0 := by
    by_contra! h
    exact he0 (hN _ (N.smul_mem _ he) h)
  have : Nontrivial R := ⟨_, _, hz0⟩
  obtain ⟨u, hu⟩ := (ht (B e z) (by simpa using hz0)).exists_left_inv
  obtain ⟨f, hf, hd⟩ : ∃ f ∈ N, B e f = 1 := ⟨u • z, N.smul_mem _ hz, by simpa using hu⟩
  have hd' : B f e = -1 := by rw [← hB.neg_eq, hd]
  let N' : Submodule R V := N ⊓ (LinearMap.ker (B e) ⊓ LinearMap.ker (B f))
  have hmem : ∀ y, y ∈ N' ↔ y ∈ N ∧ B e y = 0 ∧ B f y = 0 := fun y => Iff.rfl
  have hpr : ∀ y ∈ N, y - B y f • e - B e y • f ∈ N' := fun y hy =>
    (hmem _).2 ⟨N.sub_mem (N.sub_mem hy (N.smul_mem _ he)) (N.smul_mem _ hf),
      by simp [hd, hB.self_eq_zero], by simp [← hB.neg_eq y f, hd', hB.self_eq_zero]⟩
  have hdec : ∀ y ∈ N, ∃ a b : R, ∃ y' ∈ N', y = a • e + b • f + y' := fun y hy =>
    ⟨B y f, B e y, _, hpr y hy, by abel⟩
  obtain ⟨g, e', f', hs, hspan⟩ := ih N' (lt_of_le_of_ne inf_le_left fun h => by
      have := ((hmem f).1 (h ▸ hf)).2.1
      simp [hd] at this) (by
    intro x hx hx0
    refine hN x hx.1 fun y hy => ?_
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y hy
    simp [hx0 y' hy', hB.eq_iff.1 ((hmem x).1 hx).2.1, hB.eq_iff.1 ((hmem x).1 hx).2.2]) (by
    intro x hx hx0
    obtain ⟨a, y, hy, h₁, h₂⟩ := hF x hx.1 hx0
    have h₃ : t • (y - B y f • e - B e y • f) = t • y := by
      have h₄ : t * B y f = 0 := by
        simpa [hB.eq_iff.1 ((hmem x).1 hx).2.2] using (congrArg (B · f) h₁).symm
      have h₅ : t * B e y = 0 := by
        simpa [((hmem x).1 hx).2.1] using (congrArg (B e) h₁).symm
      simp [smul_sub, smul_smul, h₄, h₅]
    exact ⟨a, _, hpr y hy, h₃ ▸ h₁, h₃ ▸ h₂⟩)
  have he' : ∀ i, e' i ∈ N' := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hf' : ∀ i, f' i ∈ N' := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inr i, rfl⟩
  refine ⟨g + 1, Fin.cons e e', Fin.cons f f', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (he' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.1]
    · simp [hs.left_left]
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [hB.self_eq_zero]
    · simp [((hmem _).1 (hf' _)).2.2]
    · simp [hB.eq_iff.1 ((hmem _).1 (hf' _)).2.2]
    · simp [hs.right_right]
  · intro i
    cases i using Fin.cases
    · simp [hd]
    · simp [hs.left_right_self]
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact absurd rfl hij
    · simp [((hmem _).1 (hf' _)).2.1]
    · simp [hB.eq_iff.1 ((hmem _).1 (he' _)).2.2]
    · simpa using hs.left_right_ne _ _ fun a => hij (congrArg _ a)
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i | i, rfl⟩ <;> cases i using Fin.cases
      · exact he
      · exact (he' _).1
      · exact hf
      · exact (hf' _).1
    · intro y hy
      obtain ⟨a, b, y', hy', rfl⟩ := hdec y hy
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
        (Submodule.smul_mem _ _ ?_)) ?_
      · exact Submodule.subset_span ⟨Sum.inl 0, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inr 0, rfl⟩
      · rw [← hspan] at hy'
        refine Submodule.span_mono ?_ hy'
        rintro _ ⟨i | i, rfl⟩
        · exact ⟨Sum.inl i.succ, rfl⟩
        · exact ⟨Sum.inr i.succ, rfl⟩

open ReciprocityTheory.ChartRestriction.G.Out in

/- English proof (translation)
Establish `hp0` using `hp.pos`. Establish `: NeZero (p ^ (j + 1))` using `⟨by positivity⟩`. Establish `: Finite V` using `Nat.finite_of_card_ne_zero (by rw [h₀]; positivity)`. Establish `hdiv : ∀ x : V, p • x = 0 → ∃ y, p ^ j • y = x`. Set `φ : V →+ V` to `nsmulAddMonoidHom (p ^ j)`.

Set `ψ : V →+ V` to `nsmulAddMonoidHom p`. Establish `hle : φ.range ≤ ψ.ker`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `show p • p ^ j • y = 0`. Rewrite using `[smul_smul, ← pow_succ', ← Nat.cast_smul_eq_nsmul (ZMod (p ^ (j + 1))), ZMod.natCast_self, zero_smul]`.

Establish `hc : Nat.card φ.range = Nat.card ψ.ker`. Establish `h` using `AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker`. Rewrite `h` using `[Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, h₀, show Nat.card φ.ker = _ from h₁, pow_succ', mul_pow]`. Conclude with `(Nat.eq_of_mul_eq_mul_right (by positivity) h).symm.trans h₂.symm`. Use `AddSubgroup.eq_of_le_of_card_ge hle hc.ge` as an intermediate fact.

Introduce `x hx`. Conclude with `(this ▸ hx : x ∈ φ.range)`. Take `⟨g', e, f, hs, hspan⟩` from `exists_isSymplecticFamily_span hB ((p ^ j : ℕ) : ZMod (p ^ (j + 1))) (by`. Introduce `r hr`. Take `⟨m, rfl⟩` from `ZMod.natCast_zmod_surjective r`.

Use `(ZMod.isUnit_natCast_iff_not_dvd_pow hp j.succ_pos).2 ?_` and prove the remaining obligations. Introduce and unpack `⟨c, rfl⟩`. Apply `hr` to reduce the goal to its premises. Rewrite using `[← Nat.cast_mul, ← mul_assoc, ← pow_succ, Nat.cast_mul, ZMod.natCast_self, zero_mul]) ⊤`. Use the proof step `(fun x _ h => hN x fun y => h y trivial) (by`.

Introduce `x _ hx`. Establish `hex : ∃ m, p ^ m • x = 0` using `⟨j + 1, by`. Rewrite using `[← Nat.cast_smul_eq_nsmul (ZMod (p ^ (j + 1))), ZMod.natCast_self, zero_smul]⟩`. Take `⟨m, hm⟩` from `Nat.exists_eq_succ_of_ne_zero (n := Nat.find hex) (by simpa using hx)`. Establish `a₁ : p ^ (m + 1) • x = 0` using `by have := Nat.find_spec hex; rwa [hm] at this`.

Establish `a₂ : p ^ m • x ≠ 0` using `Nat.find_min hex (by omega)`. Take `⟨y, hy⟩` from `hdiv (p ^ m • x) (by rw [smul_smul, ← pow_succ', a₁])`. Conclude with `⟨(p ^ m : ℕ), y, trivial, by simp only [Nat.cast_smul_eq_nsmul, hy], by`. Rewrite using `[Nat.cast_smul_eq_nsmul, hy]⟩)` and apply the resulting hypothesis. Establish `hli : LinearIndependent (ZMod (p ^ (j + 1))) (Sum.elim e f)`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce and unpack `c hc (k | k)`. Simplify `(hs.apply_sum_right c k).symm` using `[hc]`. Simplify `(hs.apply_left_sum c k).symm` using `[hc]`. Choose the witnesses or unpack the hypotheses as in `rfl : g' = g := by`.

Establish `h` using `Nat.card_congr (Module.Basis.mk hli hspan.ge).equivFun.toEquiv`. Rewrite `h` using `[h₀, Nat.card_fun, Nat.card_zmod]`. Use `Nat.pow_right_injective (Nat.one_lt_pow j.succ_ne_zero hp.one_lt) h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers.

Set `σ : Fin (2 * g') ≃ Fin g' ⊕ Fin g'` to `(finCongr (two_mul g')).trans finSumFinEquiv.symm`. Use `⟨Sum.elim e f ∘ σ, fun i k => ?_, hli.comp σ σ.injective⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `σ.symm.surjective i`. Take `⟨b, rfl⟩` from `σ.symm.surjective k`. Simplify using `only [Function.comp, Equiv.apply_symm_apply, stdSymp]`.

Establish `l : ∀ a, (σ.symm (.inl a) : ℕ) = a` using `fun _ => rfl`. Establish `r : ∀ a, (σ.symm (.inr a) : ℕ) = g' + a` using `fun _ => rfl`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> have := a.2 <;> have := b.2 <;>`. Apply the tactic sequence `simp only [l, r, Sum.elim_inl, Sum.elim_inr, hs.left_left, hs.right_right, hs.left_right, hs.right_left hB, Fin.ext_iff] <;> split_ifs <;> first | omega | simp`.
-/
theorem exists_stdSymp_zmod {p j g : ℕ} (hp : p.Prime) {V : Type*} [AddCommGroup V] [Module (ZMod (p ^ (j + 1))) V]
    (h₀ : Nat.card V = (p ^ (j + 1)) ^ (2 * g)) (h₁ : Nat.card {x : V // p ^ j • x = 0} = (p ^ j) ^ (2 * g))
    (h₂ : Nat.card {x : V // p • x = 0} = p ^ (2 * g))
    {B : LinearMap.BilinForm (ZMod (p ^ (j + 1))) V} (hB : B.IsAlt) (hN : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∃ v : Fin (2 * g) → V, (∀ i k, B (v i) (v k) = (stdSymp g i k : ℤ)) ∧
      LinearIndependent (ZMod (p ^ (j + 1))) v := by
  have hp0 := hp.pos
  have : NeZero (p ^ (j + 1)) := ⟨by positivity⟩
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [h₀]; positivity)
  have hdiv : ∀ x : V, p • x = 0 → ∃ y, p ^ j • y = x := by
    let φ : V →+ V := nsmulAddMonoidHom (p ^ j)
    let ψ : V →+ V := nsmulAddMonoidHom p
    have hle : φ.range ≤ ψ.ker := by
      rintro _ ⟨y, rfl⟩
      show p • p ^ j • y = 0
      rw [smul_smul, ← pow_succ', ← Nat.cast_smul_eq_nsmul (ZMod (p ^ (j + 1))), ZMod.natCast_self, zero_smul]
    have hc : Nat.card φ.range = Nat.card ψ.ker := by
      have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
      rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv, h₀,
        show Nat.card φ.ker = _ from h₁, pow_succ', mul_pow] at h
      exact (Nat.eq_of_mul_eq_mul_right (by positivity) h).symm.trans h₂.symm
    have := AddSubgroup.eq_of_le_of_card_ge hle hc.ge
    intro x hx
    exact (this ▸ hx : x ∈ φ.range)
  obtain ⟨g', e, f, hs, hspan⟩ := exists_isSymplecticFamily_span hB ((p ^ j : ℕ) : ZMod (p ^ (j + 1))) (by
    intro r hr
    obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective r
    refine (ZMod.isUnit_natCast_iff_not_dvd_pow hp j.succ_pos).2 ?_
    rintro ⟨c, rfl⟩
    apply hr
    rw [← Nat.cast_mul, ← mul_assoc, ← pow_succ, Nat.cast_mul, ZMod.natCast_self, zero_mul]) ⊤
    (fun x _ h => hN x fun y => h y trivial) (by
    intro x _ hx
    have hex : ∃ m, p ^ m • x = 0 := ⟨j + 1, by
      rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ (j + 1))), ZMod.natCast_self, zero_smul]⟩
    classical
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (n := Nat.find hex) (by simpa using hx)
    have a₁ : p ^ (m + 1) • x = 0 := by have := Nat.find_spec hex; rwa [hm] at this
    have a₂ : p ^ m • x ≠ 0 := Nat.find_min hex (by omega)
    obtain ⟨y, hy⟩ := hdiv (p ^ m • x) (by rw [smul_smul, ← pow_succ', a₁])
    exact ⟨(p ^ m : ℕ), y, trivial, by simp only [Nat.cast_smul_eq_nsmul, hy], by
      rwa [Nat.cast_smul_eq_nsmul, hy]⟩)
  have hli : LinearIndependent (ZMod (p ^ (j + 1))) (Sum.elim e f) := by
    rw [Fintype.linearIndependent_iff]
    rintro c hc (k | k)
    · simpa [hc] using (hs.apply_sum_right c k).symm
    · simpa [hc] using (hs.apply_left_sum c k).symm
  obtain rfl : g' = g := by
    have h := Nat.card_congr (Module.Basis.mk hli hspan.ge).equivFun.toEquiv
    rw [h₀, Nat.card_fun, Nat.card_zmod] at h
    have := Nat.pow_right_injective (Nat.one_lt_pow j.succ_ne_zero hp.one_lt) h
    simp at this
    omega
  let σ : Fin (2 * g') ≃ Fin g' ⊕ Fin g' := (finCongr (two_mul g')).trans finSumFinEquiv.symm
  refine ⟨Sum.elim e f ∘ σ, fun i k => ?_, hli.comp σ σ.injective⟩
  obtain ⟨a, rfl⟩ := σ.symm.surjective i
  obtain ⟨b, rfl⟩ := σ.symm.surjective k
  simp only [Function.comp, Equiv.apply_symm_apply, stdSymp]
  have l : ∀ a, (σ.symm (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (σ.symm (.inr a) : ℕ) = g' + a := fun _ => rfl
  rcases a with a | a <;> rcases b with b | b <;> have := a.2 <;> have := b.2 <;>
    simp only [l, r, Sum.elim_inl, Sum.elim_inr, hs.left_left, hs.right_right, hs.left_right, hs.right_left hB,
      Fin.ext_iff] <;> split_ifs <;> first | omega | simp

open ReciprocityTheory.ChartRestriction.G.Out in

/- English proof (translation)
Break down `J with _ | j` into its components or cases. Take `rfl : ze = 1` from `by simpa using hz.pow_eq_one`. Use `⟨fun _ => 1, fun _ => one_pow _, fun _ _ => by simpa using halt 1 (one_pow _), fun c c' _ => ?_⟩` and prove the remaining obligations. Conclude with `funext fun i => Fin.ext (by have := (c i).2; have := (c' i).2; simp at *; omega)`. Establish `hp0` using `hp.pos`.

Establish `: NeZero (p ^ (j + 1))` using `⟨by positivity⟩`. Set `T : Subgroup G` to `(powMonoidHom (p ^ (j + 1))).ker`. Use `choose w hw hw' using fun x y : T => hW x y x.2 y.2`. Establish `wl : ∀ x x' y, w (x * x') y = w x y * w x' y` using `fun x x' y => (hw' _ _ _ (hmul _ _ _ _ _ (hw x y) (hw x' y))).symm`. Establish `ws : ∀ x y, w y x = (w x y)⁻¹` using `fun x y => (hw' _ _ _ (hsymm _ _ _ (hw x y))).symm`.

Establish `wr : ∀ x y y', w x (y * y') = w x y * w x y'` using `fun x y y' => by`. Rewrite using `[ws _ x, wl, mul_inv, ← ws, ← ws]`. Establish `wm : ∀ x y, w x y ∈ Subgroup.zpowers ze` using `fun x y => by`. Rewrite using `[hz.zpowers_eq, mem_rootsOfUnity]`. Use `map_pow (MonoidHom.mk' (w x) (wr x)) y (p ^ (j + 1))` as an intermediate fact.

Rewrite `this` using `[show y ^ p ^ (j + 1) = 1 from Subtype.ext y.2, map_one]`. Conclude with `this.symm`. Establish `hT : ∀ x : Additive T, p ^ (j + 1) • x = 0` using `fun x => Subtype.ext x.toMul.2`. Set `_ : Module (ZMod (p ^ (j + 1))) (Additive T)` to `AddCommGroup.zmodModule hT`. Set `β : Additive T → Additive T → ZMod (p ^ (j + 1))` to `fun x y => hz.zmodEquivZPowers.symm (Additive.ofMul ⟨w x.toMul y.toMul, wm _ _⟩)`.

Establish `βl : ∀ x x' y, β (x + x') y = β x y + β x' y` using `fun x x' y => by`. Simplify using `only [β, ← map_add]`. Conclude with `congrArg _ (Subtype.ext (wl _ _ _))`. Establish `βr : ∀ x y y', β x (y + y') = β x y + β x y'` using `fun x y y' => by`. Simplify using `only [β, ← map_add]`.

Conclude with `congrArg _ (Subtype.ext (wr _ _ _))`. Establish `βw : ∀ x y (n : ℤ), β x y = n ↔ w x.toMul y.toMul = ze ^ n` using `fun x y n => by`. Simplify using `only [β]`. Rewrite using `[AddEquiv.symm_apply_eq, hz.zmodEquivZPowers_apply_coe_int]`. Conclude with `Subtype.ext_iff`.

Set `B : LinearMap.BilinForm (ZMod (p ^ (j + 1))) (Additive T)` to `LinearMap.mk₂ _ β βl (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (β · y) fun x x' => βl x x' y) c x) βr (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (β x) (βr x)) c y)`. Establish `hcount : ∀ m, m ≤ j + 1 → Nat.card {x : Additive T // p ^ m • x = 0} = (p ^ m) ^ (2 * g)` using `fun m hm => by`. Rewrite using `[← hc m]`. Use `Nat.card_congr ⟨fun x => ⟨x.1.toMul.1, congrArg Subtype.val x.2⟩, fun x => ⟨Additive.ofMul ⟨x.1, ?_⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩` and prove the remaining obligations. Take `⟨d, hd⟩` from `pow_dvd_pow p hm`.

Use `show x.1 ^ _ = 1`. Rewrite using `[hd, pow_mul, x.2, one_pow]`. Take `⟨v, hv, hli⟩` from `exists_stdSymp_zmod (V := Additive T) (g := g) hp (hc (j + 1)) (hcount j j.le_succ) (by simpa using hcount 1 (by omega)) (B := B) (fun x => ((βw x x 0).2 (by simpa using (hw' _ _ _ (halt _ x.toMul.2)).symm)).trans Int.cast_zero) (fun x hx => Subtype.ext (hnd _ x.toMul.2 fun y hy …`. Establish `h` using `(βw x (Additive.ofMul ⟨y, hy⟩) 0).1 ((hx _).trans Int.cast_zero.symm)`. Rewrite `h` using `[zpow_zero]`.

Conclude with `h ▸ hw x.toMul ⟨y, hy⟩))`. Use `⟨fun i => (v i).toMul.1, fun i => (v i).toMul.2, fun i k => (βw _ _ _).1 (hv i k) ▸ hw _ _, fun c c' h => funext fun i => ?_⟩` and prove the remaining obligations. Establish `h' : ∑ i, ((c i : ℕ) : ZMod (p ^ (j + 1))) • v i = ∑ i, ((c' i : ℕ) : ZMod (p ^ (j + 1))) • v i`. Simplify using `only [Nat.cast_smul_eq_nsmul]`. Apply `Additive.toMul.injective` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using h`. Use `Fintype.linearIndependent_iffₛ.1 hli _ _ h' i` as an intermediate fact. Rewrite `this` using `[ZMod.natCast_eq_natCast_iff']`. Conclude with `Fin.ext (by rwa [Nat.mod_eq_of_lt (c i).2, Nat.mod_eq_of_lt (c' i).2] at this)`.
-/
theorem exists_stdSymp_of_pairing {p J g : ℕ} (hp : p.Prime) {G R : Type*} [CommGroup G] [CommRing R] [IsDomain R]
    (hc : ∀ m, Nat.card {x : G // x ^ p ^ m = 1} = (p ^ m) ^ (2 * g)) {ze : Rˣ} (hz : IsPrimitiveRoot ze (p ^ J))
    (W : G → G → Rˣ → Prop) (hW : ∀ x y, x ^ p ^ J = 1 → y ^ p ^ J = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) (halt : ∀ x, x ^ p ^ J = 1 → W x x 1)
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x, x ^ p ^ J = 1 → (∀ y, y ^ p ^ J = 1 → W x y 1) → x = 1) :
    ∃ v : Fin (2 * g) → G, (∀ i, v i ^ p ^ J = 1) ∧ (∀ i k, W (v i) (v k) (ze ^ stdSymp g i k)) ∧
      Function.Injective fun c : Fin (2 * g) → Fin (p ^ J) => ∏ i, v i ^ (c i : ℕ) := by
  rcases J with _ | j
  · obtain rfl : ze = 1 := by simpa using hz.pow_eq_one
    refine ⟨fun _ => 1, fun _ => one_pow _, fun _ _ => by simpa using halt 1 (one_pow _), fun c c' _ => ?_⟩
    exact funext fun i => Fin.ext (by have := (c i).2; have := (c' i).2; simp at *; omega)
  have hp0 := hp.pos
  have : NeZero (p ^ (j + 1)) := ⟨by positivity⟩
  let T : Subgroup G := (powMonoidHom (p ^ (j + 1))).ker
  choose w hw hw' using fun x y : T => hW x y x.2 y.2
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (hmul _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (hsymm _ _ _ (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  have wm : ∀ x y, w x y ∈ Subgroup.zpowers ze := fun x y => by
    rw [hz.zpowers_eq, mem_rootsOfUnity]
    have := map_pow (MonoidHom.mk' (w x) (wr x)) y (p ^ (j + 1))
    rw [show y ^ p ^ (j + 1) = 1 from Subtype.ext y.2, map_one] at this
    exact this.symm
  have hT : ∀ x : Additive T, p ^ (j + 1) • x = 0 := fun x => Subtype.ext x.toMul.2
  let _ : Module (ZMod (p ^ (j + 1))) (Additive T) := AddCommGroup.zmodModule hT
  let β : Additive T → Additive T → ZMod (p ^ (j + 1)) := fun x y =>
    hz.zmodEquivZPowers.symm (Additive.ofMul ⟨w x.toMul y.toMul, wm _ _⟩)
  have βl : ∀ x x' y, β (x + x') y = β x y + β x' y := fun x x' y => by
    simp only [β, ← map_add]
    exact congrArg _ (Subtype.ext (wl _ _ _))
  have βr : ∀ x y y', β x (y + y') = β x y + β x y' := fun x y y' => by
    simp only [β, ← map_add]
    exact congrArg _ (Subtype.ext (wr _ _ _))
  have βw : ∀ x y (n : ℤ), β x y = n ↔ w x.toMul y.toMul = ze ^ n := fun x y n => by
    simp only [β]
    rw [AddEquiv.symm_apply_eq, hz.zmodEquivZPowers_apply_coe_int]
    exact Subtype.ext_iff
  let B : LinearMap.BilinForm (ZMod (p ^ (j + 1))) (Additive T) := LinearMap.mk₂ _ β βl
    (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (β · y) fun x x' => βl x x' y) c x) βr
    (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (β x) (βr x)) c y)
  have hcount : ∀ m, m ≤ j + 1 → Nat.card {x : Additive T // p ^ m • x = 0} = (p ^ m) ^ (2 * g) := fun m hm => by
    rw [← hc m]
    refine Nat.card_congr ⟨fun x => ⟨x.1.toMul.1, congrArg Subtype.val x.2⟩,
      fun x => ⟨Additive.ofMul ⟨x.1, ?_⟩, Subtype.ext x.2⟩, fun _ => rfl, fun _ => rfl⟩
    obtain ⟨d, hd⟩ := pow_dvd_pow p hm
    show x.1 ^ _ = 1
    rw [hd, pow_mul, x.2, one_pow]
  obtain ⟨v, hv, hli⟩ := exists_stdSymp_zmod (V := Additive T) (g := g) hp (hc (j + 1)) (hcount j j.le_succ)
    (by simpa using hcount 1 (by omega)) (B := B)
    (fun x => ((βw x x 0).2 (by simpa using (hw' _ _ _ (halt _ x.toMul.2)).symm)).trans Int.cast_zero)
    (fun x hx => Subtype.ext (hnd _ x.toMul.2 fun y hy => by
      have h := (βw x (Additive.ofMul ⟨y, hy⟩) 0).1 ((hx _).trans Int.cast_zero.symm)
      rw [zpow_zero] at h
      exact h ▸ hw x.toMul ⟨y, hy⟩))
  refine ⟨fun i => (v i).toMul.1, fun i => (v i).toMul.2, fun i k => (βw _ _ _).1 (hv i k) ▸ hw _ _,
    fun c c' h => funext fun i => ?_⟩
  have h' : ∑ i, ((c i : ℕ) : ZMod (p ^ (j + 1))) • v i = ∑ i, ((c' i : ℕ) : ZMod (p ^ (j + 1))) • v i := by
    simp only [Nat.cast_smul_eq_nsmul]
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa using h
  have := Fintype.linearIndependent_iffₛ.1 hli _ _ h' i
  rw [ZMod.natCast_eq_natCast_iff'] at this
  exact Fin.ext (by rwa [Nat.mod_eq_of_lt (c i).2, Nat.mod_eq_of_lt (c' i).2] at this)

end GlobalTheory.LevelExist

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `hL K _ _ P n J hn hK ze hz`. Use `P.isAb.comm` as an intermediate fact. Establish `: IsDomain Γ(Spec (CommRingCat.of K), ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _`. Establish `hcard : ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (s : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K)) (m : ℕ), Nat.card {x : Over.mk s ⟶ P.A // x ^ n ^ m = 1} = (n ^ m) ^ (2 * P.g)` using `fun K' _ _ s m => (hL.mulN _ P (n ^ m) (Nat.one_le_pow _ _ hn.pos)).2.2.2.2 K' s (by`. Rewrite using `[Nat.cast_pow, ← map_natCast (Spec.preimage s).hom]`.

Conclude with `pow_ne_zero _ ((map_ne_zero _).2 hK))`. Take `⟨w₁, w₂, w₃, -⟩` from `hL.weil _ P (n ^ J) (baseOver _)`. Take `⟨v, hv, hw, hinj⟩` from `LevelExist.exists_stdSymp_of_pairing (G := baseOver _ ⟶ P.A) (g := P.g) hn (hcard K (𝟙 _)) hz (fun x y c => WeilIs P.A P.L (n ^ J : ℕ) x y c) w₁ w₂ w₃ (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) (hL.weilNondeg K P _ (by rw [Nat.cast_pow]; exact pow_ne_zero _ hK))`. Establish `hind : ∀ (K' : Type) [Field K'] (s : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K)), Function.Injective fun c : Fin (2 * P.g) → Fin (n ^ J) => linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver _) ≫ v i) (fun i => (c i : ℕ))`. Introduce `K' _ s c c' h`.

Establish `: Surjective s` using `⟨fun z => ⟨(default : PrimeSpectrum K'), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩`. Establish `: Epi s` using `Flat.epi_of_flat_of_surjective s`. Set `b : Over.mk s ⟶ baseOver _` to `Over.homMk s (by simp)`. Set `φ : (baseOver _ ⟶ P.A) →* (Over.mk s ⟶ P.A)` to `MonoidHom.mk' (b ≫ ·) fun _ _ => MonObj.comp_mul _ _ _`. Establish `e : ∀ c : Fin (2 * P.g) → Fin (n ^ J), linComb (fun i => b ≫ v i) (fun i => (c i : ℕ)) = φ (∏ i, v i ^ (c i : ℕ))` using `fun c => by`.

Rewrite using `[linComb, List.prod_ofFn, map_prod]`. Simplify using `only [map_pow]`. Both sides reduce to the same expression. Establish `h'` using `(e c).symm.trans (h.trans (e c'))`. Conclude with `hinj (Over.OverMorphism.ext ((cancel_epi s).1 (congrArg (fun q => q.left) h')))`.

Use `⟨⟨v, hz, hv, fun K' _ _ s => hind K' s, fun K' _ _ s y hy => ?_, hw⟩⟩` and prove the remaining obligations. Set `F : (Fin (2 * P.g) → Fin (n ^ J)) → {x : Over.mk s ⟶ P.A // x ^ n ^ J = 1}` to `fun c => ⟨linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver _) ≫ v i) (fun i => (c i : ℕ)), by`. Rewrite using `[linComb, List.prod_ofFn, ← Finset.prod_pow]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, Nat.mul_comm, pow_mul, ← MonObj.comp_pow, hv, MonObj.comp_one, one_pow]⟩`.

Establish `: Finite {x : Over.mk s ⟶ P.A // x ^ n ^ J = 1}` using `Nat.finite_of_card_ne_zero (by rw [hcard]; have := hn.pos; positivity)`. Establish `hF : Function.Bijective F` using `(Nat.bijective_iff_injective_and_card F).2 ⟨fun c c' h => hind K' s (congrArg Subtype.val h), by rw [hcard]; simp⟩`. Take `⟨c, hc⟩` from `hF.2 ⟨y, hy⟩`. Conclude with `⟨c, congrArg Subtype.val hc⟩`.
-/
theorem nonempty_level_prime_pow : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) (n J : ℕ), n.Prime → (n : K) ≠ 0 →
    ∀ ze : Γ(Spec (CommRingCat.of K), ⊤)ˣ, IsPrimitiveRoot ze (n ^ J) → Nonempty (Level P (n ^ J) ze) := by
  intro hL K _ _ P n J hn hK ze hz
  have := P.isAb.comm
  have : IsDomain Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have hcard : ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (s : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
      (m : ℕ), Nat.card {x : Over.mk s ⟶ P.A // x ^ n ^ m = 1} = (n ^ m) ^ (2 * P.g) := fun K' _ _ s m =>
    (hL.mulN _ P (n ^ m) (Nat.one_le_pow _ _ hn.pos)).2.2.2.2 K' s (by
      rw [Nat.cast_pow, ← map_natCast (Spec.preimage s).hom]
      exact pow_ne_zero _ ((map_ne_zero _).2 hK))
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P (n ^ J) (baseOver _)
  obtain ⟨v, hv, hw, hinj⟩ := LevelExist.exists_stdSymp_of_pairing (G := baseOver _ ⟶ P.A) (g := P.g) hn
    (hcard K (𝟙 _)) hz (fun x y c => WeilIs P.A P.L (n ^ J : ℕ) x y c) w₁ w₂ w₃
    (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h)
    (hL.weilNondeg K P _ (by rw [Nat.cast_pow]; exact pow_ne_zero _ hK))
  have hind : ∀ (K' : Type) [Field K'] (s : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K)),
      Function.Injective fun c : Fin (2 * P.g) → Fin (n ^ J) => linComb (fun i =>
        (Over.homMk s (by simp) : Over.mk s ⟶ baseOver _) ≫ v i) (fun i => (c i : ℕ)) := by
    intro K' _ s c c' h
    have : Surjective s := ⟨fun z => ⟨(default : PrimeSpectrum K'), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
    have : Epi s := Flat.epi_of_flat_of_surjective s
    let b : Over.mk s ⟶ baseOver _ := Over.homMk s (by simp)
    let φ : (baseOver _ ⟶ P.A) →* (Over.mk s ⟶ P.A) := MonoidHom.mk' (b ≫ ·) fun _ _ => MonObj.comp_mul _ _ _
    have e : ∀ c : Fin (2 * P.g) → Fin (n ^ J),
        linComb (fun i => b ≫ v i) (fun i => (c i : ℕ)) = φ (∏ i, v i ^ (c i : ℕ)) := fun c => by
      rw [linComb, List.prod_ofFn, map_prod]
      simp only [map_pow]
      rfl
    have h' := (e c).symm.trans (h.trans (e c'))
    exact hinj (Over.OverMorphism.ext ((cancel_epi s).1 (congrArg (fun q => q.left) h')))
  refine ⟨⟨v, hz, hv, fun K' _ _ s => hind K' s, fun K' _ _ s y hy => ?_, hw⟩⟩
  let F : (Fin (2 * P.g) → Fin (n ^ J)) → {x : Over.mk s ⟶ P.A // x ^ n ^ J = 1} := fun c =>
    ⟨linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver _) ≫ v i) (fun i => (c i : ℕ)), by
      rw [linComb, List.prod_ofFn, ← Finset.prod_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [← pow_mul, Nat.mul_comm, pow_mul, ← MonObj.comp_pow, hv, MonObj.comp_one, one_pow]⟩
  have : Finite {x : Over.mk s ⟶ P.A // x ^ n ^ J = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; have := hn.pos; positivity)
  have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨fun c c' h => hind K' s (congrArg Subtype.val h), by rw [hcard]; simp⟩
  obtain ⟨c, hc⟩ := hF.2 ⟨y, hy⟩
  exact ⟨c, congrArg Subtype.val hc⟩

end GlobalTheory
