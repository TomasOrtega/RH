import Mathlib
open scoped Classical

namespace GlobalTheory

/- English proof (translation)
Establish `hT : Tq.Finite`. Set `e : Q → ∀ p : s, O p` to `fun c p => Φ c p`. Establish `hfin : (Set.pi Set.univ (fun p : s => U p)).Finite` using `Set.Finite.pi (fun p => hU p p.2)`. Use `Set.Finite.of_finite_image (f := e) (hfin.subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩ p _`.

Conclude with `hmem c hc p p.2`. Introduce `c hc c' hc' h`. Conclude with `hinj c hc c' hc' (fun p hp => congrFun h ⟨p, hp⟩)`. Use `⟨hT, ?_⟩` and prove the remaining obligations. Set `t : ∀ p, Finset (O p)` to `fun p => if h : p ∈ s then (hU p h).toFinset else ∅`.

Establish `ht : ∀ p ∈ s, ∀ o, o ∈ t p ↔ o ∈ U p`. Introduce `p hp o`. Simplify using `[t, hp]`. Rewrite using `[tsum_eq_sum (s := hT.toFinset) (fun c hc => by`. Rewrite `hc` using `[Set.Finite.mem_toFinset]`.

Simplify using `[hc])]`. Establish `hR : ∀ p ∈ s, (∑' o : O p, if o ∈ U p then g p o else 0) = ∑ o ∈ t p, g p o`. Introduce `p hp`. Rewrite using `[tsum_eq_sum (s := t p) (fun o ho => by rw [ht p hp] at ho; simp [ho])]`. Use `Finset.sum_congr rfl (fun o ho => ?_)` and prove the remaining obligations.

Rewrite `ho` using `[ht p hp]`. Simplify using `[ho]`. Rewrite using `[Finset.prod_congr rfl hR, Finset.prod_sum]`. Establish `hL : (∑ c ∈ hT.toFinset, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0) = ∑ c ∈ hT.toFinset, ∏ p ∈ s, g p (Φ c p)` using `Finset.sum_congr rfl (fun c hc => by rw [Set.Finite.mem_toFinset] at hc; simp [hc])`. Rewrite using `[hL]`.

Use `Finset.sum_bij (fun c _ => fun p _ => Φ c p) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `c hc`. Rewrite `hc` using `[Set.Finite.mem_toFinset]`. Rewrite using `[Finset.mem_pi]`. Introduce `p hp`.

Conclude with `(ht p hp _).2 (hmem c hc p hp)`. Introduce `c hc c' hc' h`. Rewrite `hc`, `hc'` using `[Set.Finite.mem_toFinset]`. Conclude with `hinj c hc c' hc' (fun p hp => congrFun (congrFun h p) hp)`. Introduce `x hx`.

Rewrite `hx` using `[Finset.mem_pi]`. Set `y : ∀ p, O p` to `fun p => if h : p ∈ s then x p h else Classical.arbitrary (O p)`. Take `⟨c, hc, hcy⟩` from `hsurj y (fun p hp => by`. Simplify using `only [y, dif_pos hp]`. Conclude with `(ht p hp _).1 (hx p hp))`.

Use `⟨c, (Set.Finite.mem_toFinset hT).2 hc, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p hp`. Rewrite using `[hcy p hp]`. Simplify using `[y, hp]`. Introduce `c _`.

Conclude with `(Finset.prod_attach s (fun p => g p (Φ c p))).symm`.
-/
theorem prod_sum_of_local_choices {ι Q R : Type} {O : ι → Type} [CommSemiring R] [TopologicalSpace R] [∀ p, Nonempty (O p)]
    (s : Finset ι) (Φ : Q → ∀ p, O p) (Tq : Set Q) (U : ∀ p, Set (O p))
    (hU : ∀ p ∈ s, (U p).Finite)
    (hinj : ∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c')
    (hmem : ∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p)
    (hsurj : ∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p)
    (g : ∀ p, O p → R) :
    Tq.Finite ∧ (∑' c : Q, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0)
      = ∏ p ∈ s, ∑' o : O p, if o ∈ U p then g p o else 0 := by
  have hT : Tq.Finite := by
    let e : Q → ∀ p : s, O p := fun c p => Φ c p
    have hfin : (Set.pi Set.univ (fun p : s => U p)).Finite :=
      Set.Finite.pi (fun p => hU p p.2)
    refine Set.Finite.of_finite_image (f := e) (hfin.subset ?_) ?_
    · rintro _ ⟨c, hc, rfl⟩ p _
      exact hmem c hc p p.2
    · intro c hc c' hc' h
      exact hinj c hc c' hc' (fun p hp => congrFun h ⟨p, hp⟩)
  refine ⟨hT, ?_⟩
  let t : ∀ p, Finset (O p) := fun p => if h : p ∈ s then (hU p h).toFinset else ∅
  have ht : ∀ p ∈ s, ∀ o, o ∈ t p ↔ o ∈ U p := by
    intro p hp o; simp [t, hp]
  rw [tsum_eq_sum (s := hT.toFinset) (fun c hc => by
    rw [Set.Finite.mem_toFinset] at hc; simp [hc])]
  have hR : ∀ p ∈ s, (∑' o : O p, if o ∈ U p then g p o else 0) = ∑ o ∈ t p, g p o := by
    intro p hp
    rw [tsum_eq_sum (s := t p) (fun o ho => by rw [ht p hp] at ho; simp [ho])]
    refine Finset.sum_congr rfl (fun o ho => ?_)
    rw [ht p hp] at ho; simp [ho]
  rw [Finset.prod_congr rfl hR, Finset.prod_sum]
  have hL : (∑ c ∈ hT.toFinset, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0)
      = ∑ c ∈ hT.toFinset, ∏ p ∈ s, g p (Φ c p) :=
    Finset.sum_congr rfl (fun c hc => by rw [Set.Finite.mem_toFinset] at hc; simp [hc])
  rw [hL]
  refine Finset.sum_bij (fun c _ => fun p _ => Φ c p) ?_ ?_ ?_ ?_
  · intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    rw [Finset.mem_pi]
    intro p hp
    exact (ht p hp _).2 (hmem c hc p hp)
  · intro c hc c' hc' h
    rw [Set.Finite.mem_toFinset] at hc hc'
    exact hinj c hc c' hc' (fun p hp => congrFun (congrFun h p) hp)
  · intro x hx
    rw [Finset.mem_pi] at hx
    let y : ∀ p, O p := fun p => if h : p ∈ s then x p h else Classical.arbitrary (O p)
    obtain ⟨c, hc, hcy⟩ := hsurj y (fun p hp => by
      simp only [y, dif_pos hp]; exact (ht p hp _).1 (hx p hp))
    refine ⟨c, (Set.Finite.mem_toFinset hT).2 hc, ?_⟩
    funext p hp
    rw [hcy p hp]; simp [y, hp]
  · intro c _
    exact (Finset.prod_attach s (fun p => g p (Φ c p))).symm

end GlobalTheory
