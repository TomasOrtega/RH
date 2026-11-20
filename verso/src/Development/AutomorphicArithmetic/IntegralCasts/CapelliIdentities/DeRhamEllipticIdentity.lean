import Mathlib

/- English proof (translation)
Introduce `K S _ _ _ _ _ _ ω f₀ h`. Take `⟨U, hU, hfix⟩` from `h`. Establish `hmul : ∀ (a b : K) (v : S), ω (a * b) v = ω a (ω b v)`. Introduce `a b v`. Rewrite using `[map_mul, Module.End.mul_apply]`.

Set `H : Subgroup K` to `{ carrier := {k | ω k f₀ = f₀} one_mem' := by simp mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[hmul, hb, ha]`. Use the proof step `inv_mem' := by`.

Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Establish `h1 : ω a⁻¹ (ω a f₀) = f₀`. Rewrite using `[← hmul]`. Simplify using the standard rewrite rules.

Rewrite using `[ha] at h1 }` and apply the resulting hypothesis. Establish `hmem : ∀ k, k ∈ H ↔ ω k f₀ = f₀` using `fun k => Iff.rfl`. Establish `hopen : IsOpen (H : Set K)` using `H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hU (fun k hk => hfix k hk))`. Use `haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hopen`. Use `haveI : Fintype (K ⧸ H) := Fintype.ofFinite _`.

Set `F : K ⧸ H → S` to `fun q => ω q.out f₀`. Establish `hF : ∀ (g : K) (q : K ⧸ H), ω g (F q) = F (g • q)`. Introduce `g q`. Establish `hq : ((g * q.out : K) : K ⧸ H) = g • q` using `by conv_rhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression.

Establish `hq' : (((g • q).out : K) : K ⧸ H) = ((g * q.out : K) : K ⧸ H)`. Rewrite using `[hq, QuotientGroup.out_eq']`. Establish `hh : ((g • q).out)⁻¹ * (g * q.out) ∈ H` using `QuotientGroup.eq.mp hq'`. Establish `h2 : g * q.out = (g • q).out * (((g • q).out)⁻¹ * (g * q.out))` using `by group`. Express the relevant statement in the definitionally equal form `ω g (ω q.out f₀) = ω (g • q).out f₀`.

Rewrite using `[← hmul, h2, hmul, (hmem _).mp hh]`. Take `⟨m, hm⟩ : ∃ m, Fintype.card (K ⧸ H) = m + 1` from `Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero`. Set `e : Fin (m + 1) ≃ K ⧸ H` to `(Fintype.equivFinOfCardEq hm).symm`. Use `⟨m, fun i => (e i).out, fun g => ?_⟩` and prove the remaining obligations. Establish `hsum : ∑ i : Fin (m + 1), ω (e i).out f₀ = ∑ q, F q` using `Equiv.sum_comp e F`.

Rewrite using `[hsum, map_sum]`. Repeatedly rewrite using `[hF]`. Conclude with `Equiv.sum_comp (MulAction.toPerm g) F`.
-/
theorem UpperTheory.Reformulated.B.InvariantSumOfTranslates.main :
    ∀ {K S : Type} [inst : Group K] [inst_1 : TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [inst_4 : AddCommGroup S] [inst_5 : _root_.Module ℂ S] (ω : K →* Module.End ℂ S) (f₀ : S),
      (∃ U ∈ nhds (1 : K), ∀ k ∈ U, ((ω : K → Module.End ℂ S) k : S → S) f₀ = f₀) →
        ∃ (m : ℕ) (k : Fin (m + (1 : ℕ)) → K),
          ∀ (g : K),
            ((ω : K → Module.End ℂ S) g : S → S) (∑ i : Fin (m + (1 : ℕ)), ((ω : K → Module.End ℂ S) (k i) : S → S) f₀) =
              ∑ i : Fin (m + (1 : ℕ)), ((ω : K → Module.End ℂ S) (k i) : S → S) f₀ := by
  intro K S _ _ _ _ _ _ ω f₀ h
  obtain ⟨U, hU, hfix⟩ := h
  have hmul : ∀ (a b : K) (v : S), ω (a * b) v = ω a (ω b v) := by
    intro a b v
    rw [map_mul, Module.End.mul_apply]

  let H : Subgroup K :=
    { carrier := {k | ω k f₀ = f₀}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [hmul, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ω a⁻¹ (ω a f₀) = f₀ := by
          rw [← hmul]; simp
        rwa [ha] at h1 }
  have hmem : ∀ k, k ∈ H ↔ ω k f₀ = f₀ := fun k => Iff.rfl
  have hopen : IsOpen (H : Set K) :=
    H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hU (fun k hk => hfix k hk))
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hopen
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _

  let F : K ⧸ H → S := fun q => ω q.out f₀
  have hF : ∀ (g : K) (q : K ⧸ H), ω g (F q) = F (g • q) := by
    intro g q
    have hq : ((g * q.out : K) : K ⧸ H) = g • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hq' : (((g • q).out : K) : K ⧸ H) = ((g * q.out : K) : K ⧸ H) := by
      rw [hq, QuotientGroup.out_eq']
    have hh : ((g • q).out)⁻¹ * (g * q.out) ∈ H := QuotientGroup.eq.mp hq'
    have h2 : g * q.out = (g • q).out * (((g • q).out)⁻¹ * (g * q.out)) := by group
    change ω g (ω q.out f₀) = ω (g • q).out f₀
    rw [← hmul, h2, hmul, (hmem _).mp hh]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card (K ⧸ H) = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : Fin (m + 1) ≃ K ⧸ H := (Fintype.equivFinOfCardEq hm).symm
  refine ⟨m, fun i => (e i).out, fun g => ?_⟩
  have hsum : ∑ i : Fin (m + 1), ω (e i).out f₀ = ∑ q, F q := Equiv.sum_comp e F
  rw [hsum, map_sum]
  simp_rw [hF]
  exact Equiv.sum_comp (MulAction.toPerm g) F
