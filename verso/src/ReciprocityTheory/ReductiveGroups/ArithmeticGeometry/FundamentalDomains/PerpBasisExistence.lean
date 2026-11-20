import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExistsUnitaryBasisSameFlag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianPairingAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermEqZeroOfTraceFormVanish
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalComplementLines
import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement

namespace ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Simplify using `only [herm, Pi.add_apply, HermitianPairingAlgebra.cc_add, mul_add, Finset.sum_add_distrib]`.
-/
lemma herm_add_right' (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp only [herm, Pi.add_apply, HermitianPairingAlgebra.cc_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [herm]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HermitianPairingAlgebra.herm_add_left, ih]`.
-/
lemma herm_sum_left' (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (f : ι → Fin r → E) (y : Fin r → E) : herm G (∑ i ∈ s, f i) y = ∑ i ∈ s, herm G (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HermitianPairingAlgebra.herm_add_left, ih]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [herm, cc]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_right', ih]`.
-/
lemma herm_sum_right' (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (f : ι → Fin r → E) (x : Fin r → E) : herm G x (∑ i ∈ s, f i) = ∑ i ∈ s, herm G x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm, cc]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_right', ih]

/- English proof (translation)
Repeatedly rewrite using `[herm_sum_left', HermitianPairingAlgebra.herm_smul_left, herm_sum_right', HermitianPairingAlgebra.herm_smul_right, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
lemma herm_comb (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p q : Fin n → E) (f : Fin n → Fin r → E) :
    herm G (∑ i, p i • f i) (∑ j, q j • f j) = ∑ i, ∑ j, p i * herm G (f i) (f j) * cc (q j) := by
  simp_rw [herm_sum_left', HermitianPairingAlgebra.herm_smul_left, herm_sum_right', HermitianPairingAlgebra.herm_smul_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def hxi (G : Matrix (Fin r) (Fin r) E) (ξ : Fin r → E) : (Fin r → E) →ₗ[E] E where
  toFun x := herm G x ξ
  map_add' x y := HermitianTraceFormVanishing.herm_add_left G x y ξ
  map_smul' a x := HermitianTraceFormVanishing.herm_smul_left G a x ξ

/- English proof (translation)
Use `set f := hxi X.Gm ξ with hf`. Establish `hfx : ∀ x, f x = herm X.Gm x ξ` using `fun _ => rfl`. Establish `hw : (fun b => cc (ξ b)) ≠ 0`. Introduce `h`. Apply `hξ0` to reduce the goal to its premises.

Use function extensionality and compare the values at `b`. Establish `hb` using `congrFun h b`. Simplify using `only [Pi.zero_apply, cc] at hb`. Simplify using `using hb`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, (X.Gm *ᵥ fun b => cc (ξ b)) a ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hw (Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det (funext h))`. Establish `hfa : f (Pi.single a 1) ≠ 0`. Rewrite using `[hfx]`.

Use `ha using 1` and compare the differences between its conclusion and the goal. Simplify using `[herm, Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hsurj : Function.Surjective f` using `fun y => ⟨(y / f (Pi.single a 1)) • Pi.single a 1, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfa]⟩`. Use `set K := LinearMap.ker f with hK`. Establish `hξK : ξ ∈ K` using `by rw [LinearMap.mem_ker, hfx]; exact hξξ`.

Establish `hrange : Module.finrank E (LinearMap.range f) = 1`. Rewrite using `[LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]`. Establish `hKr : Module.finrank E K = r - 1`. Use `LinearMap.finrank_range_add_finrank_ker f` as an intermediate fact. Rewrite `this` using `[hrange, Module.finrank_fin_fun]`.

Establish `h2 : 1 + Module.finrank E K = r` using `this`. Use linear arithmetic over natural numbers and integers. Establish `hKpos : 0 < Module.finrank E K`. Rewrite using `[Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]`. Introduce `h`.

Apply `hξ0` to reduce the goal to its premises. Establish `: ξ ∈ (⊥ : Submodule E (Fin r → E))` using `h ▸ hξK`. Simplify using `using this`. Establish `hr2 : 2 ≤ r` using `by omega`. Use `set ξK : K := ⟨ξ, hξK⟩ with hξKdef`.

Establish `hξK0 : ξK ≠ 0` using `fun h => hξ0 (congrArg Subtype.val h)`. Use `set S : Submodule E K := E ∙ ξK with hS`. Establish `hQ : Module.finrank E (K ⧸ S) = r - 2`. Establish `h0` using `Submodule.finrank_quotient_add_finrank S`. Establish `h1 : Module.finrank E S = 1` using `by rw [hS]; exact finrank_span_singleton hξK0`.

Rewrite `h0` using `[h1, hKr]`. Establish `h2 : Module.finrank E (K ⧸ S) + 1 = r - 1` using `h0`. Use linear arithmetic over natural numbers and integers. Set `bQ` to `Module.finBasisOfFinrankEq E (K ⧸ S) hQ`. Set `βK : Fin (r - 2) → K` to `fun k => (Submodule.Quotient.mk_surjective S (bQ k)).choose`.

Establish `hβK : ∀ k, Submodule.Quotient.mk (p` using `S) (βK k) = bQ k := fun k => (Submodule.Quotient.mk_surjective S (bQ k)).choose_spec`. Establish `hdecK : ∀ y : K, ∃ (c : Fin (r - 2) → E) (e : E), y = ∑ k, c k • βK k + e • ξK`. Introduce `y`. Use `set c := bQ.repr (Submodule.Quotient.mk y) with hc`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Establish `hmk : Submodule.Quotient.mk (p` using `S) (∑ k, c k • βK k) = ∑ k, c k • bQ k := by`. Establish `h` using `map_sum S.mkQ (fun k => c k • βK k) Finset.univ`. Simplify using `only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, hβK] at h`. Conclude with `h`. Establish `hq : Submodule.Quotient.mk (p` using `S) y = Submodule.Quotient.mk (∑ k, c k • βK k) := by`.

Rewrite using `[hmk, hc, bQ.sum_repr]`. Rewrite `hq` using `[Submodule.Quotient.eq]`. Establish `hq' : y - ∑ k, c k • βK k ∈ E ∙ ξK` using `hq`. Take `⟨e, he⟩` from `Submodule.mem_span_singleton.mp hq'`. Conclude with `⟨e, by rw [he]; abel⟩`.

Use `⟨fun k => (βK k : Fin r → E), fun k => (βK k).2, ?_, ?_⟩` and prove the remaining obligations. Establish `hspan : ⊤ ≤ Submodule.span E (Set.range (Fin.cons ξK βK : Fin (r - 2 + 1) → K))`. Introduce `y _`. Take `⟨c, e, rfl⟩` from `hdecK y`. Use `Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)` and prove the remaining obligations.

Conclude with `Submodule.subset_span ⟨k.succ, by simp⟩`. Conclude with `Submodule.subset_span ⟨0, by simp⟩`. Establish `hli` using `linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by rw [Fintype.card_fin, hKr]; omega)`. Establish `hmap` using `hli.map' K.subtype (Submodule.ker_subtype K)`. Establish `heq : (K.subtype ∘ (Fin.cons ξK βK : Fin (r - 2 + 1) → K)) = (Fin.cons ξ (fun k => (βK k : Fin r → E)) : Fin (r - 2 + 1) → Fin r → E)`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun k => ?_) i <;> simp [ξK]`. Conclude with `heq ▸ hmap`. Introduce `x hx`. Establish `hxK : x ∈ K` using `by rw [LinearMap.mem_ker, hfx]; exact hx`.

Take `⟨c, e, he⟩` from `hdecK ⟨x, hxK⟩`. Use `⟨c, e, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val he` as an intermediate fact. Simplify `this` using `[ξK]`.
-/
theorem exists_beta (X : Data E r) {ξ : Fin r → E} (hξξ : herm X.Gm ξ ξ = 0) (hξ0 : ξ ≠ 0) :
    ∃ β : Fin (r - 2) → Fin r → E, (∀ k, herm X.Gm (β k) ξ = 0) ∧
      LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E) ∧
      (∀ x : Fin r → E, herm X.Gm x ξ = 0 →
        ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ) := by
  classical
  set f := hxi X.Gm ξ with hf
  have hfx : ∀ x, f x = herm X.Gm x ξ := fun _ => rfl

  have hw : (fun b => cc (ξ b)) ≠ 0 := by
    intro h
    apply hξ0
    funext b
    have hb := congrFun h b
    simp only [Pi.zero_apply, cc] at hb
    simpa using hb
  obtain ⟨a, ha⟩ : ∃ a, (X.Gm *ᵥ fun b => cc (ξ b)) a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det (funext h))
  have hfa : f (Pi.single a 1) ≠ 0 := by
    rw [hfx]
    convert ha using 1
    simp [herm, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hsurj : Function.Surjective f := fun y =>
    ⟨(y / f (Pi.single a 1)) • Pi.single a 1, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfa]⟩
  set K := LinearMap.ker f with hK
  have hξK : ξ ∈ K := by rw [LinearMap.mem_ker, hfx]; exact hξξ
  have hrange : Module.finrank E (LinearMap.range f) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hKr : Module.finrank E K = r - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange, Module.finrank_fin_fun] at this
    have h2 : 1 + Module.finrank E K = r := this
    omega
  have hKpos : 0 < Module.finrank E K := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h
    apply hξ0
    have : ξ ∈ (⊥ : Submodule E (Fin r → E)) := h ▸ hξK
    simpa using this
  have hr2 : 2 ≤ r := by omega
  set ξK : K := ⟨ξ, hξK⟩ with hξKdef
  have hξK0 : ξK ≠ 0 := fun h => hξ0 (congrArg Subtype.val h)
  set S : Submodule E K := E ∙ ξK with hS
  have hQ : Module.finrank E (K ⧸ S) = r - 2 := by
    have h0 := Submodule.finrank_quotient_add_finrank S
    have h1 : Module.finrank E S = 1 := by rw [hS]; exact finrank_span_singleton hξK0
    rw [h1, hKr] at h0
    have h2 : Module.finrank E (K ⧸ S) + 1 = r - 1 := h0
    omega
  let bQ := Module.finBasisOfFinrankEq E (K ⧸ S) hQ
  let βK : Fin (r - 2) → K := fun k => (Submodule.Quotient.mk_surjective S (bQ k)).choose
  have hβK : ∀ k, Submodule.Quotient.mk (p := S) (βK k) = bQ k := fun k =>
    (Submodule.Quotient.mk_surjective S (bQ k)).choose_spec
  have hdecK : ∀ y : K, ∃ (c : Fin (r - 2) → E) (e : E), y = ∑ k, c k • βK k + e • ξK := by
    intro y
    set c := bQ.repr (Submodule.Quotient.mk y) with hc
    refine ⟨c, ?_⟩
    have hmk : Submodule.Quotient.mk (p := S) (∑ k, c k • βK k) = ∑ k, c k • bQ k := by
      have h := map_sum S.mkQ (fun k => c k • βK k) Finset.univ
      simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, hβK] at h
      exact h
    have hq : Submodule.Quotient.mk (p := S) y = Submodule.Quotient.mk (∑ k, c k • βK k) := by
      rw [hmk, hc, bQ.sum_repr]
    rw [Submodule.Quotient.eq] at hq
    have hq' : y - ∑ k, c k • βK k ∈ E ∙ ξK := hq
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hq'
    exact ⟨e, by rw [he]; abel⟩
  refine ⟨fun k => (βK k : Fin r → E), fun k => (βK k).2, ?_, ?_⟩
  · have hspan : ⊤ ≤ Submodule.span E (Set.range (Fin.cons ξK βK : Fin (r - 2 + 1) → K)) := by
      intro y _
      obtain ⟨c, e, rfl⟩ := hdecK y
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
        (Submodule.smul_mem _ _ ?_)
      · exact Submodule.subset_span ⟨k.succ, by simp⟩
      · exact Submodule.subset_span ⟨0, by simp⟩
    have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan
      (by rw [Fintype.card_fin, hKr]; omega)
    have hmap := hli.map' K.subtype (Submodule.ker_subtype K)
    have heq : (K.subtype ∘ (Fin.cons ξK βK : Fin (r - 2 + 1) → K)) =
        (Fin.cons ξ (fun k => (βK k : Fin r → E)) : Fin (r - 2 + 1) → Fin r → E) := by
      funext i
      refine Fin.cases ?_ (fun k => ?_) i <;> simp [ξK]
    exact heq ▸ hmap
  · intro x hx
    have hxK : x ∈ K := by rw [LinearMap.mem_ker, hfx]; exact hx
    obtain ⟨c, e, he⟩ := hdecK ⟨x, hxK⟩
    refine ⟨c, e, ?_⟩
    have := congrArg Subtype.val he
    simpa [ξK] using this

variable (X : DataX E r)

def LBsub {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {c | ∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L'}
  add_mem' := by
    rintro c c' ⟨e, he⟩ ⟨e', he'⟩
    refine ⟨e + e', ?_⟩
    have h : ∑ k, (c + c') k • β k + (e + e') • ξ =
        (∑ k, c k • β k + e • ξ) + (∑ k, c' k • β k + e' • ξ) := by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      abel
    rw [h]
    exact X.L'.add_mem he he'
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a c ⟨e, he⟩
    refine ⟨(a : E) * e, ?_⟩
    have h : ∑ k, (a • c) k • β k + ((a : E) * e) • ξ = a • (∑ k, c k • β k + e • ξ) := by
      rw [integer_smul_eq_coe_smul a c, integer_smul_eq_coe_smul a (∑ k, c k • β k + e • ξ)]
      simp only [Pi.smul_apply, smul_eq_mul, smul_add, Finset.smul_sum, mul_smul]
    rw [h]
    exact X.L'.smul_mem a he

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
lemma mem_LBsub {n : ℕ} (β : Fin n → Fin r → E) (ξ : Fin r → E) (c : Fin n → E) :
    c ∈ LBsub X β ξ ↔ ∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L' := Iff.rfl

end

end ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
