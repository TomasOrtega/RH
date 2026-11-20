import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TestCover

section Ring

variable {S : Type*} [CommRing S]

/- English proof (translation)
Take `⟨x, y, hxy⟩` from `Ideal.mem_span_pair.1 (Ideal.eq_top_iff_one _ |>.1 h)`. Prove the components needed by the constructor for the conclusion. Establish `e : d = x * (d * f) + (d * y) * g`. Take the linear combination `(-d) * hxy`. Rewrite using `[e]`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g))`. Establish `e : 1 - d = ((1 - d) * x) * f + y * ((1 - d) * g)`. Take the linear combination `(-(1 - d)) * hxy`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)) (Ideal.mul_mem_left _ _ h2)`.
-/
theorem mem_of_compare {f g d : S} (h : Ideal.span {f, g} = ⊤) (h1 : d * f ∈ Ideal.span {g})
    (h2 : (1 - d) * g ∈ Ideal.span {f}) : d ∈ Ideal.span {g} ∧ 1 - d ∈ Ideal.span {f} := by
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 (Ideal.eq_top_iff_one _ |>.1 h)
  constructor
  · have e : d = x * (d * f) + (d * y) * g := by
      linear_combination (-d) * hxy
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1)
      (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g))
  · have e : 1 - d = ((1 - d) * x) * f + y * ((1 - d) * g) := by
      linear_combination (-(1 - d)) * hxy
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))
      (Ideal.mul_mem_left _ _ h2)

/- English proof (translation)
Unfold `IsIdempotentElem`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => h k`.
-/
theorem idem_prod {ι : Type*} (t : Finset ι) (f : ι → S) (h : ∀ k, IsIdempotentElem (f k)) :
    IsIdempotentElem (∏ k ∈ t, f k) := by
  unfold IsIdempotentElem
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => h k

/- English proof (translation)
Rewrite using `[Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem]`. Establish `hk : ∀ k, Ideal.Quotient.mk (Ideal.span (Set.range e)) (1 - e k) = 1` using `fun k => by`. Establish `h0 : Ideal.Quotient.mk (Ideal.span (Set.range e)) (e k) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self k))`. Rewrite using `[map_sub, map_one, h0, sub_zero]`. Use `congrArg (Ideal.Quotient.mk (Ideal.span (Set.range e))) h` as an intermediate fact.

Rewrite `this` using `[map_prod, Finset.prod_congr rfl fun k _ => hk k, Finset.prod_const_one, map_zero]`. Rewrite using `[map_one, this]`.
-/
theorem span_top_of_prod {m : ℕ} (e : Fin m → S) (h : ∏ k, (1 - e k) = 0) :
    Ideal.span (Set.range e) = ⊤ := by
  rw [Ideal.eq_top_iff_one, ← Ideal.Quotient.eq_zero_iff_mem]
  have hk : ∀ k, Ideal.Quotient.mk (Ideal.span (Set.range e)) (1 - e k) = 1 := fun k => by
    have h0 : Ideal.Quotient.mk (Ideal.span (Set.range e)) (e k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self k))
    rw [map_sub, map_one, h0, sub_zero]
  have := congrArg (Ideal.Quotient.mk (Ideal.span (Set.range e))) h
  rw [map_prod, Finset.prod_congr rfl fun k _ => hk k, Finset.prod_const_one, map_zero] at this
  rw [map_one, this]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `s c _ hc`. Establish `h0 : c = 0`.

Rewrite `hc` using `[Set.range_eq_empty, Ideal.span_empty]`. Conclude with `(Submodule.mem_bot _).1 hc`. Conclude with `⟨Fin.elim0, fun k => k.elim0, fun k => k.elim0, by rw [h0, zero_mul]⟩`. Consider the case `succ m ih`. Introduce `s c hc hcs`.

Establish `hr : Set.range s = insert (s 0) (Set.range (Fin.tail s))` using `by conv_lhs => rw [← Fin.cons_self_tail s]`. Conclude with `Fin.range_cons _ _`. Rewrite `hcs` using `[hr, Ideal.mem_span_insert]`. Take `⟨a, r, hr', hcr⟩` from `hcs`. Establish `htop : Ideal.span {s 0, r + (1 - c)} = ⊤`.

Rewrite using `[Ideal.eq_top_iff_one, Ideal.mem_span_pair]`. Conclude with `⟨a, 1, by linear_combination -hcr⟩`. Take `⟨d, hd, h1, h2⟩` from `hV _ _ htop`. Take `⟨hdg, hds⟩` from `mem_of_compare htop h1 h2`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 hdg`.

Establish `hcc : c * c = c` using `hc`. Establish `hcd : IsIdempotentElem (c * d)` using `hc.mul hd`. Establish `hmem : c * d ∈ Ideal.span (Set.range (Fin.tail s))`. Establish `e : c * d = (t * c) * r`. Rewrite using `[← ht]`.

Take the linear combination `(-t) * hcc`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ hr'`. Take `⟨e', hi, hm, hp⟩` from `ih (Fin.tail s) (c * d) hcd hmem`. Use `⟨Fin.cons (1 - d) e', ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `k`. Use `Fin.cases ?_ (fun i => ?_) k` and prove the remaining obligations. Simplify using `using hd.one_sub`. Simplify using `using hi i`. Introduce `k`.

Use `Fin.cases ?_ (fun i => ?_) k` and prove the remaining obligations. Simplify using `using hds`. Simplify `hm i` using `[Fin.tail]`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`.

Take the linear combination `hp`.
-/
theorem idem_refine
    (hV : ∀ f g : S, Ideal.span {f, g} = ⊤ →
      ∃ e : S, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f}) :
    ∀ (m : ℕ) (s : Fin m → S) (c : S), IsIdempotentElem c → c ∈ Ideal.span (Set.range s) →
      ∃ e : Fin m → S, (∀ k, IsIdempotentElem (e k)) ∧ (∀ k, e k ∈ Ideal.span {s k}) ∧
        c * ∏ k, (1 - e k) = 0 := by
  intro m
  induction m with
  | zero =>
    intro s c _ hc
    have h0 : c = 0 := by
      rw [Set.range_eq_empty, Ideal.span_empty] at hc
      exact (Submodule.mem_bot _).1 hc
    exact ⟨Fin.elim0, fun k => k.elim0, fun k => k.elim0, by rw [h0, zero_mul]⟩
  | succ m ih =>
    intro s c hc hcs
    have hr : Set.range s = insert (s 0) (Set.range (Fin.tail s)) := by
      conv_lhs => rw [← Fin.cons_self_tail s]
      exact Fin.range_cons _ _
    rw [hr, Ideal.mem_span_insert] at hcs
    obtain ⟨a, r, hr', hcr⟩ := hcs
    have htop : Ideal.span {s 0, r + (1 - c)} = ⊤ := by
      rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
      exact ⟨a, 1, by linear_combination -hcr⟩
    obtain ⟨d, hd, h1, h2⟩ := hV _ _ htop
    obtain ⟨hdg, hds⟩ := mem_of_compare htop h1 h2
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hdg
    have hcc : c * c = c := hc
    have hcd : IsIdempotentElem (c * d) := hc.mul hd
    have hmem : c * d ∈ Ideal.span (Set.range (Fin.tail s)) := by
      have e : c * d = (t * c) * r := by
        rw [← ht]
        linear_combination (-t) * hcc
      rw [e]
      exact Ideal.mul_mem_left _ _ hr'
    obtain ⟨e', hi, hm, hp⟩ := ih (Fin.tail s) (c * d) hcd hmem
    refine ⟨Fin.cons (1 - d) e', ?_, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa using hd.one_sub
      · simpa using hi i
    · intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa using hds
      · simpa [Fin.tail] using hm i
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      linear_combination hp

end Ring

/- English proof (translation)
Introduce `l _ A hA m s hs`. Establish `hV : ∀ f g : A.U, Ideal.span {f, g} = ⊤ → ∃ e : A.U, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f}` using `fun f g h => hA.val_aic.1 f g ⟨0, by rw [pow_zero, h]; trivial⟩`. Take `⟨u, hi, hm, hp⟩` from `idem_refine hV m s 1 IsIdempotentElem.one (by rw [hs]; trivial)`. Rewrite `hp` using `[one_mul]`. Establish `hex : ∀ k, ∃ e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = u k` using `fun k => (RL.idem_au A (u k) (hi k)).exists`.

Use `choose e he hsh using hex`. Establish `hc` using `(RL.sharp_cong A).2.2`. Establish `hzero : A.sharp 0 = 0`. Use `hc 1 IsIdempotentElem.one` as an intermediate fact. Rewrite `this` using `[sub_self, map_one, sub_self]`. Then use the resulting hypothesis.

Establish `hsp : A.sharp (∏ k, (1 - e k)) = 0`. Rewrite using `[map_prod, ← hp]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [hc _ (he k), hsh]`. Establish `hidem : IsIdempotentElem (∏ k, (1 - e k))` using `idem_prod _ _ fun k => (he k).one_sub`. Establish `h0 : ∏ k, (1 - e k) = 0` using `(RL.idem_au A 0 IsIdempotentElem.zero).unique ⟨hidem, hsp⟩ ⟨IsIdempotentElem.zero, hzero⟩`.

Conclude with `⟨e, he, span_top_of_prod e h0, fun k => by rw [hsh]; exact hm k⟩`.
-/
theorem test_cover : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.IsTest → ∀ {m : ℕ} (s : Fin m → A.U),
    Ideal.span (Set.range s) = ⊤ → ∃ e : Fin m → A.A, (∀ k, IsIdempotentElem (e k)) ∧
      Ideal.span (Set.range e) = ⊤ ∧ ∀ k, A.sharp (e k) ∈ Ideal.span {s k} := by
  intro l _ A hA m s hs
  have hV : ∀ f g : A.U, Ideal.span {f, g} = ⊤ →
      ∃ e : A.U, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f} :=
    fun f g h => hA.val_aic.1 f g ⟨0, by rw [pow_zero, h]; trivial⟩
  obtain ⟨u, hi, hm, hp⟩ := idem_refine hV m s 1 IsIdempotentElem.one (by rw [hs]; trivial)
  rw [one_mul] at hp
  have hex : ∀ k, ∃ e₀ : A.A, IsIdempotentElem e₀ ∧ A.sharp e₀ = u k := fun k =>
    (RL.idem_au A (u k) (hi k)).exists
  choose e he hsh using hex
  have hc := (RL.sharp_cong A).2.2
  have hzero : A.sharp 0 = 0 := by
    have := hc 1 IsIdempotentElem.one
    rwa [sub_self, map_one, sub_self] at this
  have hsp : A.sharp (∏ k, (1 - e k)) = 0 := by
    rw [map_prod, ← hp]
    exact Finset.prod_congr rfl fun k _ => by rw [hc _ (he k), hsh]
  have hidem : IsIdempotentElem (∏ k, (1 - e k)) :=
    idem_prod _ _ fun k => (he k).one_sub
  have h0 : ∏ k, (1 - e k) = 0 :=
    (RL.idem_au A 0 IsIdempotentElem.zero).unique ⟨hidem, hsp⟩ ⟨IsIdempotentElem.zero, hzero⟩
  exact ⟨e, he, span_top_of_prod e h0, fun k => by rw [hsh]; exact hm k⟩

end GlobalTheory.CompanionTheory.TestCover
