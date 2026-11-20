import Formalism.LocalToGlobal.ProjectiveLattices.LocalUnitReduction.FinRedStatement

namespace Formalism.L2.Pj.LocalUnitReduction

section

variable {K' Fr : Type*} [Field K'] [CommRing Fr] [Algebra K' Fr] (J : Ideal Fr)
  {ι : Type*} {R : ι → Type*} [∀ c, CommRing (R c)] [∀ c, Algebra K' (R c)]
  (φ : ∀ c, Fr →ₐ[K'] R c)

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `hne : Ideal.span {Ideal.Quotient.mk I p} ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]` and apply the resulting hypothesis. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ hne`. Use `haveI := hM.isPrime`.

Use `hp (M.comap (Ideal.Quotient.mk I)) inferInstance (fun x hx => ?_) ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]`. Conclude with `M.zero_mem`. Conclude with `hle (Ideal.mem_span_singleton_self _)`.
-/
theorem isUnit_mk_of_forall_prime {I : Ideal Fr} {p : Fr}
    (hp : ∀ Q : Ideal Fr, Q.IsPrime → I ≤ Q → p ∉ Q) : IsUnit (Ideal.Quotient.mk I p) := by
  by_contra h
  have hne : Ideal.span {Ideal.Quotient.mk I p} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI := hM.isPrime
  refine hp (M.comap (Ideal.Quotient.mk I)) inferInstance (fun x hx => ?_) ?_
  · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact M.zero_mem
  · exact hle (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Establish `key : ∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q → ∀ y ∈ Ideal.map (φ c) J, ∃ s g : Fr, s ∉ Q ∧ g ∈ J ∧ φ c s * y = φ c g`. Introduce `Q hQ hJQ hkQ y hy`. Establish `h1Q : (1 : Fr) ∉ Q` using `fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)`. Establish `hy' : y ∈ Submodule.span (R c) (φ c '' J)` using `hy`. Use `clear hy`.

Proceed by induction on `hy' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, hj, rfl⟩` from `hx`. Conclude with `⟨1, j, h1Q, hj, by simp⟩`. Consider the case `zero => exact ⟨1, 0, h1Q, J.zero_mem, by simp⟩`.

Consider the case `add y1 y2 _ _ ih1 ih2`. Take `⟨s1, g1, hs1, hg1, e1⟩` from `ih1`. Take `⟨s2, g2, hs2, hg2, e2⟩` from `ih2`. Use `⟨s1 * s2, s2 * g1 + s1 * g2, fun h => (hQ.mem_or_mem h).elim hs1 hs2, J.add_mem (J.mul_mem_left _ hg1) (J.mul_mem_left _ hg2), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_add, map_mul, map_mul, ← e1, ← e2]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `smul r y _ ih`. Take `⟨s, g, hs, hg, e⟩` from `ih`. Take `⟨a, p, hp, ep⟩` from `hloc r`. Use `⟨p * s, a * g, fun h => (hQ.mem_or_mem h).elim (hp Q hQ hJQ hkQ) hs, J.mul_mem_left _ hg, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_eq_mul, map_mul, map_mul, ← e, ← ep]`. Expand and normalize the polynomial expressions, which then agree. Assume the negation of the conclusion as `hfL`. Set `C : Ideal Fr` to `{ carrier := {x | x * f ∈ J ⊔ RingHom.ker (φ c)} add_mem' := fun {a b} ha hb => by`. Simplify `(J ⊔ RingHom.ker (φ c)).add_mem ha hb` using `[add_mul]`.

Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun r x hx => by`. Simplify `(J ⊔ RingHom.ker (φ c)).mul_mem_left r hx }` using `[smul_eq_mul, mul_assoc]`. Establish `hC : C ≠ ⊤` using `fun h => by`. Establish `h1 : (1 : Fr) ∈ C` using `h ▸ Submodule.mem_top`.

Conclude with `hfL (by simpa [C] using h1)`. Take `⟨Q, hQ, hCQ⟩` from `Ideal.exists_le_maximal C hC`. Establish `hLC : J ⊔ RingHom.ker (φ c) ≤ C` using `fun x hx => (show x * f ∈ J ⊔ RingHom.ker (φ c) from (J ⊔ RingHom.ker (φ c)).mul_mem_right f hx)`. Establish `hLQ` using `hLC.trans hCQ`. Take `⟨s, g, hs, hg, e⟩` from `key Q hQ.isPrime (le_sup_left.trans hLQ) (le_sup_right.trans hLQ) (φ c f) hf`.

Apply `hs` to reduce the goal to its premises. Apply `hCQ` to reduce the goal to its premises. Use `show s * f ∈ J ⊔ RingHom.ker (φ c)`. Establish `hk : s * f - g ∈ RingHom.ker (φ c)`. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, e, sub_self]`.

Establish `hsum` using `(J ⊔ RingHom.ker (φ c)).add_mem (Submodule.mem_sup_left hg) (Submodule.mem_sup_right hk)`. Simplify using `using hsum`.
-/
theorem mem_sup_ker {c : ι}
    (hloc : ∀ r : R c, ∃ a p : Fr,
      (∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q → p ∉ Q) ∧ φ c p * r = φ c a)
    {f : Fr} (hf : φ c f ∈ Ideal.map (φ c) J) : f ∈ J ⊔ RingHom.ker (φ c) := by
  have key : ∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → RingHom.ker (φ c) ≤ Q →
      ∀ y ∈ Ideal.map (φ c) J, ∃ s g : Fr, s ∉ Q ∧ g ∈ J ∧ φ c s * y = φ c g := by
    intro Q hQ hJQ hkQ y hy
    have h1Q : (1 : Fr) ∉ Q := fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)
    have hy' : y ∈ Submodule.span (R c) (φ c '' J) := hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨1, j, h1Q, hj, by simp⟩
    | zero => exact ⟨1, 0, h1Q, J.zero_mem, by simp⟩
    | add y1 y2 _ _ ih1 ih2 =>
      obtain ⟨s1, g1, hs1, hg1, e1⟩ := ih1
      obtain ⟨s2, g2, hs2, hg2, e2⟩ := ih2
      refine ⟨s1 * s2, s2 * g1 + s1 * g2, fun h => (hQ.mem_or_mem h).elim hs1 hs2,
        J.add_mem (J.mul_mem_left _ hg1) (J.mul_mem_left _ hg2), ?_⟩
      rw [map_mul, map_add, map_mul, map_mul, ← e1, ← e2]
      ring
    | smul r y _ ih =>
      obtain ⟨s, g, hs, hg, e⟩ := ih
      obtain ⟨a, p, hp, ep⟩ := hloc r
      refine ⟨p * s, a * g, fun h => (hQ.mem_or_mem h).elim (hp Q hQ hJQ hkQ) hs,
        J.mul_mem_left _ hg, ?_⟩
      rw [smul_eq_mul, map_mul, map_mul, ← e, ← ep]
      ring
  by_contra hfL
  let C : Ideal Fr :=
    { carrier := {x | x * f ∈ J ⊔ RingHom.ker (φ c)}
      add_mem' := fun {a b} ha hb => by
        simpa [add_mul] using (J ⊔ RingHom.ker (φ c)).add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun r x hx => by
        simpa [smul_eq_mul, mul_assoc] using (J ⊔ RingHom.ker (φ c)).mul_mem_left r hx }
  have hC : C ≠ ⊤ := fun h => by
    have h1 : (1 : Fr) ∈ C := h ▸ Submodule.mem_top
    exact hfL (by simpa [C] using h1)
  obtain ⟨Q, hQ, hCQ⟩ := Ideal.exists_le_maximal C hC
  have hLC : J ⊔ RingHom.ker (φ c) ≤ C := fun x hx =>
    (show x * f ∈ J ⊔ RingHom.ker (φ c) from (J ⊔ RingHom.ker (φ c)).mul_mem_right f hx)
  have hLQ := hLC.trans hCQ
  obtain ⟨s, g, hs, hg, e⟩ :=
    key Q hQ.isPrime (le_sup_left.trans hLQ) (le_sup_right.trans hLQ) (φ c f) hf
  apply hs
  apply hCQ
  show s * f ∈ J ⊔ RingHom.ker (φ c)
  have hk : s * f - g ∈ RingHom.ker (φ c) := by
    rw [RingHom.mem_ker, map_sub, map_mul, e, sub_self]
  have hsum := (J ⊔ RingHom.ker (φ c)).add_mem (Submodule.mem_sup_left hg) (Submodule.mem_sup_right hk)
  simpa using hsum

/- English proof (translation)
Assume the negation of the conclusion as `hfJ`. Set `C : Ideal Fr` to `{ carrier := {x | x * f ∈ J} add_mem' := fun {a b} ha hb => by simpa [add_mul] using J.add_mem ha hb zero_mem' := by simp smul_mem' := fun r x hx => by simpa [smul_eq_mul, mul_assoc] using J.mul_mem_left r hx }`. Establish `hC : C ≠ ⊤` using `fun h => by`. Establish `h1 : (1 : Fr) ∈ C` using `h ▸ Submodule.mem_top`. Conclude with `hfJ (by simpa [C] using h1)`.

Take `⟨Q, hQ, hCQ⟩` from `Ideal.exists_le_maximal C hC`. Use `haveI := hQ.isPrime`. Establish `hJQ : J ≤ Q` using `fun x hx => hCQ (show x * f ∈ J from J.mul_mem_right f hx)`. Establish `h1Q : (1 : Fr) ∉ Q` using `fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)`. Establish `ht : ∀ c, ∃ t : Fr, (¬ RingHom.ker (φ c) ≤ Q → t ∈ RingHom.ker (φ c)) ∧ t ∉ Q`.

Introduce `c`. Distinguish the cases in `h : RingHom.ker (φ c) ≤ Q`. Conclude with `⟨1, fun h' => absurd h h', h1Q⟩`. Take `⟨t, htk, htQ⟩` from `Set.not_subset.mp h`. Conclude with `⟨t, fun _ => htk, htQ⟩`.

Use `choose t ht2 htQ using ht`. Establish `hTQ : ∏ c, t c ∉ Q` using `fun h => by`. Take `⟨c, -, hc⟩` from `Ideal.IsPrime.prod_mem_iff.mp h`. Conclude with `htQ c hc`. Establish `hTk : ∀ c, ¬ RingHom.ker (φ c) ≤ Q → φ c (∏ c, t c) = 0` using `fun c hc => by`.

Rewrite using `[map_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ c) ((RingHom.mem_ker).mp (ht2 c hc))`. Distinguish the cases in `h0 : ∃ c0, RingHom.ker (φ c0) ≤ Q`. Take `⟨c0, hc0⟩` from `h0`. Take `⟨j, hj, k0, hk0, rfl⟩` from `Submodule.mem_sup.mp (hf c0)`.

Establish `hTk0 : (∏ c, t c) * k0 = 0` using `hinj _ fun c => by`. Distinguish the cases in `hc : c = c0`. Substitute `hc` using the available equality. Rewrite using `[map_mul, (RingHom.mem_ker).mp hk0, mul_zero]`. Establish `hcQ : ¬ RingHom.ker (φ c) ≤ Q` using `fun h => hc (hone Q hQ.isPrime hJQ c c0 h hc0)`.

Rewrite using `[map_mul, hTk c hcQ, zero_mul]`. Apply `hTQ` to reduce the goal to its premises. Apply `hCQ` to reduce the goal to its premises. Use `show (∏ c, t c) * (j + k0) ∈ J`. Rewrite using `[mul_add, hTk0, add_zero]`.

Conclude with `J.mul_mem_left _ hj`. Use `push_neg at h0`. Establish `hT0 : ∏ c, t c = 0` using `hinj _ fun c => hTk c (h0 c)`. Conclude with `hTQ (hT0 ▸ Q.zero_mem)`.
-/
theorem mem_of_forall_sup_ker [Fintype ι] (hinj : ∀ f : Fr, (∀ c, φ c f = 0) → f = 0)
    (hone : ∀ Q : Ideal Fr, Q.IsPrime → J ≤ Q → ∀ c c', RingHom.ker (φ c) ≤ Q →
      RingHom.ker (φ c') ≤ Q → c = c')
    {f : Fr} (hf : ∀ c, f ∈ J ⊔ RingHom.ker (φ c)) : f ∈ J := by
  classical
  by_contra hfJ
  let C : Ideal Fr :=
    { carrier := {x | x * f ∈ J}
      add_mem' := fun {a b} ha hb => by simpa [add_mul] using J.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun r x hx => by simpa [smul_eq_mul, mul_assoc] using J.mul_mem_left r hx }
  have hC : C ≠ ⊤ := fun h => by
    have h1 : (1 : Fr) ∈ C := h ▸ Submodule.mem_top
    exact hfJ (by simpa [C] using h1)
  obtain ⟨Q, hQ, hCQ⟩ := Ideal.exists_le_maximal C hC
  haveI := hQ.isPrime
  have hJQ : J ≤ Q := fun x hx => hCQ (show x * f ∈ J from J.mul_mem_right f hx)
  have h1Q : (1 : Fr) ∉ Q := fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h1)
  have ht : ∀ c, ∃ t : Fr, (¬ RingHom.ker (φ c) ≤ Q → t ∈ RingHom.ker (φ c)) ∧ t ∉ Q := by
    intro c
    by_cases h : RingHom.ker (φ c) ≤ Q
    · exact ⟨1, fun h' => absurd h h', h1Q⟩
    · obtain ⟨t, htk, htQ⟩ := Set.not_subset.mp h
      exact ⟨t, fun _ => htk, htQ⟩
  choose t ht2 htQ using ht
  have hTQ : ∏ c, t c ∉ Q := fun h => by
    obtain ⟨c, -, hc⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact htQ c hc
  have hTk : ∀ c, ¬ RingHom.ker (φ c) ≤ Q → φ c (∏ c, t c) = 0 := fun c hc => by
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) ((RingHom.mem_ker).mp (ht2 c hc))
  by_cases h0 : ∃ c0, RingHom.ker (φ c0) ≤ Q
  · obtain ⟨c0, hc0⟩ := h0
    obtain ⟨j, hj, k0, hk0, rfl⟩ := Submodule.mem_sup.mp (hf c0)
    have hTk0 : (∏ c, t c) * k0 = 0 := hinj _ fun c => by
      by_cases hc : c = c0
      · subst hc
        rw [map_mul, (RingHom.mem_ker).mp hk0, mul_zero]
      · have hcQ : ¬ RingHom.ker (φ c) ≤ Q := fun h => hc (hone Q hQ.isPrime hJQ c c0 h hc0)
        rw [map_mul, hTk c hcQ, zero_mul]
    apply hTQ
    apply hCQ
    show (∏ c, t c) * (j + k0) ∈ J
    rw [mul_add, hTk0, add_zero]
    exact J.mul_mem_left _ hj
  · push_neg at h0
    have hT0 : ∏ c, t c = 0 := hinj _ fun c => hTk c (h0 c)
    exact hTQ (hT0 ▸ Q.zero_mem)

end

/- English proof (translation)
Introduce `K' Fr _ _ _ J ι _ R _ _ φ hinj hone hloc hfin`. Set `Ψ : Fr ⧸ J →ₐ[K'] (∀ c, R c ⧸ Ideal.map (φ c) J)` to `Pi.algHom _ _ fun c => Ideal.quotientMapₐ (Ideal.map (φ c) J) (φ c) Ideal.le_comap_map`. Establish `hinjΨ : Function.Injective Ψ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Use `mem_of_forall_sup_ker J φ hinj hone fun c => mem_sup_ker J φ (hloc c) ?_` and prove the remaining obligations. Establish `hc` using `congr_fun hx c`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hc`. Use `haveI : ∀ c, FiniteDimensional K' (R c ⧸ Ideal.map (φ c) J) := fun c => (hfin c).1`. Use `haveI : ∀ c, IsReduced (R c ⧸ Ideal.map (φ c) J) := fun c => (hfin c).2`. Conclude with `⟨FiniteDimensional.of_injective Ψ.toLinearMap hinjΨ, isReduced_of_injective Ψ hinjΨ⟩`.
-/
theorem finRed : FinRedStatement := by
  intro K' Fr _ _ _ J ι _ R _ _ φ hinj hone hloc hfin
  let Ψ : Fr ⧸ J →ₐ[K'] (∀ c, R c ⧸ Ideal.map (φ c) J) :=
    Pi.algHom _ _ fun c => Ideal.quotientMapₐ (Ideal.map (φ c) J) (φ c) Ideal.le_comap_map
  have hinjΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine mem_of_forall_sup_ker J φ hinj hone fun c => mem_sup_ker J φ (hloc c) ?_
    have hc := congr_fun hx c
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hc
  haveI : ∀ c, FiniteDimensional K' (R c ⧸ Ideal.map (φ c) J) := fun c => (hfin c).1
  haveI : ∀ c, IsReduced (R c ⧸ Ideal.map (φ c) J) := fun c => (hfin c).2
  exact ⟨FiniteDimensional.of_injective Ψ.toLinearMap hinjΨ, isReduced_of_injective Ψ hinjΨ⟩

end Formalism.L2.Pj.LocalUnitReduction
