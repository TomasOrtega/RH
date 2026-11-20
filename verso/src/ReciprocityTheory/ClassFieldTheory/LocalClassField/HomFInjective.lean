import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CurriedCoboundaryEq

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2

open ReciprocityTheory.Coh ReciprocityTheory.Coh.InflationRestrictionInvariants ReciprocityTheory.Gal Cx Function

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Introduce `t t' h`. Use `Subtype.ext (funext fun v => ?_)` and prove the remaining obligations. Use `choose v' hv' using fun i => hφ (v i)`. Use `congrFun (congrArg Subtype.val h) v'` as an intermediate fact. Establish `h2 : P.u (t.1 fun i => P.φ (v' i)) = P.u (t'.1 fun i => P.φ (v' i))` using `this`.

Establish `h3 : (fun i => P.φ (v' i)) = v` using `funext hv'`. Rewrite `h2` using `[h3]`. Conclude with `hu h2`.
-/
theorem hom_f_injective {G' : Type u} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {M : TRep R G} {M' : TRep R G'} (P : Pair M M') (hφ : Surjective P.φ) (hu : Injective P.u) (n : ℕ) :
    Injective (P.hom.f n) := by
  intro t t' h
  refine Subtype.ext (funext fun v => ?_)
  choose v' hv' using fun i => hφ (v i)
  have := congrFun (congrArg Subtype.val h) v'
  have h2 : P.u (t.1 fun i => P.φ (v' i)) = P.u (t'.1 fun i => P.φ (v' i)) := this
  have h3 : (fun i => P.φ (v' i)) = v := funext hv'
  rw [h3] at h2
  exact hu h2

variable (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)

/- English proof (translation)
Establish `hφa : ∀ a, P.φ a = (a : G ⧸ N)` using `fun a => by rw [hP.1]; rfl`. Use `show P.u (z.1 _) = P.u (z.1 _)`. Use `congrArg (fun v => P.u (z.1 v)) (funext fun i => ?_)` and prove the remaining obligations. Use `fin_cases i`. Conclude with `hφa g`.

Conclude with `hφa h`.
-/
theorem cur_inf (hP : IsInvRep M N Q P) (z : Q.coch.X 2) (g h : G) :
    cur M (P.hom.f 2 z) g h = P.u (cur Q z (g : G ⧸ N) (h : G ⧸ N)) := by
  have hφa : ∀ a, P.φ a = (a : G ⧸ N) := fun a => by rw [hP.1]; rfl
  show P.u (z.1 _) = P.u (z.1 _)
  refine congrArg (fun v => P.u (z.1 v)) (funext fun i => ?_)
  fin_cases i
  · exact hφa g
  · exact hφa h

/- English proof (translation)
Rewrite using `[hP.1]`. Conclude with `QuotientGroup.mk'_surjective N`.
-/
theorem phi_surjective (hP : IsInvRep M N Q P) : Surjective P.φ := by
  rw [hP.1]; exact QuotientGroup.mk'_surjective N

/- English proof (translation)
Establish `: DiscreteTopology (G ⧸ N)` using `QuotientGroup.discreteTopology hN`. Establish `hC` using `fun n hn g h => stepC (isTwoCocycle_curried M x hx) (fun n hn g => (h0 n hn g).1) (fun n hn g => (h0 n hn g).2) n hn g h`. Establish `hmem : ∀ g h, ∃ q, P.u q = cur M x g h` using `fun g h => (hP.2.2 _).2 fun n hn => (hC n hn g h).2.2`. Use `choose F0 hF0 using hmem`. Set `z : Q.coch.X 2` to `⟨fun v => F0 (v 0).out (v 1).out, continuous_of_discreteTopology⟩`.

Establish `hz : P.hom.f 2 z = x`. Use `ext2 M fun g h => ?_` and prove the remaining obligations. Rewrite using `[cur_inf M N Q P hP]`. Use `show P.u (F0 (g : G ⧸ N).out (h : G ⧸ N).out) = _`. Take `⟨a, ha⟩` from `QuotientGroup.mk_out_eq_mul N g`.

Take `⟨b, hb⟩` from `QuotientGroup.mk_out_eq_mul N h`. Rewrite using `[hF0, ha, hb, (hC _ a.2 _ _).2.1, (hC _ b.2 _ _).1]`. Use `⟨z, ?_, hz⟩` and prove the remaining obligations. Apply `hom_f_injective P (phi_surjective M N Q P hP) hP.2.1.injective 3` to reduce the goal to its premises. Rewrite using `[P.hom.comm, hz, hx, map_zero]`.
-/
theorem descend2 (hN : IsOpen (N : Set G)) (hP : IsInvRep M N Q P) (x : M.coch.X 2) (hx : M.coch.d 2 x = 0)
    (h0 : ∀ n ∈ N, ∀ g, cur M x n g = 0 ∧ cur M x g n = 0) :
    ∃ z : Q.coch.X 2, Q.coch.d 2 z = 0 ∧ P.hom.f 2 z = x := by
  have : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hN
  have hC := fun n hn g h => stepC (isTwoCocycle_curried M x hx) (fun n hn g => (h0 n hn g).1) (fun n hn g => (h0 n hn g).2)
    n hn g h
  have hmem : ∀ g h, ∃ q, P.u q = cur M x g h := fun g h => (hP.2.2 _).2 fun n hn => (hC n hn g h).2.2
  choose F0 hF0 using hmem
  let z : Q.coch.X 2 := ⟨fun v => F0 (v 0).out (v 1).out, continuous_of_discreteTopology⟩
  have hz : P.hom.f 2 z = x := by
    refine ext2 M fun g h => ?_
    rw [cur_inf M N Q P hP]
    show P.u (F0 (g : G ⧸ N).out (h : G ⧸ N).out) = _
    obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul N g
    obtain ⟨b, hb⟩ := QuotientGroup.mk_out_eq_mul N h
    rw [hF0, ha, hb, (hC _ a.2 _ _).2.1, (hC _ b.2 _ _).1]
  refine ⟨z, ?_, hz⟩
  apply hom_f_injective P (phi_surjective M N Q P hP) hP.2.1.injective 3
  rw [P.hom.comm, hz, hx, map_zero]

/- English proof (translation)
Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Rewrite `hy` using `[H_mk, mk_eq_zero_iff]`.

Establish `hx` using `(memZ _).1 x.2`. Take `⟨w, hw⟩` from `norm_all M N hN h1 x.1 hx hy`. Take `⟨z, hz, hzx⟩` from `descend2 M N Q P hN hP _ (d_sub_d M x.1 hx w) hw`. Use `⟨Submodule.Quotient.mk ⟨z, (memZ _).2 hz⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[H_mk, Submodule.Quotient.eq, Submodule.mem_comap]`.

Use `show P.hom.f 2 z - x.1 ∈ M.coch.B 2`. Rewrite using `[hzx, memB]`. Conclude with `⟨-w, by rw [map_neg]; abel⟩`. Introduce and unpack `⟨y0, rfl⟩`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ y0`.

Rewrite using `[H_mk, H_mk, mk_eq_zero_iff, memB]`. Establish `hinv : ∀ n ∈ N, M.rho n (P.u (cur Q z.1 1 1)) = P.u (cur Q z.1 1 1)` using `(hP.2.2 _).1 ⟨_, rfl⟩`. Use `⟨mk1 (M.resSub N) (fun _ => P.u (cur Q z.1 1 1)) continuous_const, ?_⟩` and prove the remaining obligations. Use `ext2 (M.resSub N) fun a b => ?_` and prove the remaining obligations. Use `(curried_coboundary_eq (M.resSub N) _ continuous_const a b).trans ?_` and prove the remaining obligations.

Establish `e : cur (M.resSub N) ((Pair.res M N.subtype continuous_subtype_val).hom.Z 2 (P.hom.Z 2 z)).1 a b = cur M (P.hom.f 2 z.1) a b`. Use `congrArg (P.hom.f 2 z.1).1 (funext fun i => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> rfl`. Rewrite using `[e, cur_inf M N Q P hP, (QuotientGroup.eq_one_iff _).2 a.2, (QuotientGroup.eq_one_iff _).2 b.2]`. Simplify using `only [D1]`.

Use `hinv a a.2` as an intermediate fact. Establish `h' : (M.resSub N).rho a (P.u (cur Q z.1 1 1)) = P.u (cur Q z.1 1 1)` using `this`. Rewrite using `[h']`. Normalize the expressions using the abelian group laws.
-/
theorem exact2 (hN : IsOpen (N : Set G)) (hP : IsInvRep M N Q P) (h1 : Subsingleton ((M.resSub N).H 1)) :
    Exact (P.hom.H 2) ((Pair.res M N.subtype continuous_subtype_val).hom.H 2) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [H_mk, mk_eq_zero_iff] at hy
    have hx := (memZ _).1 x.2
    obtain ⟨w, hw⟩ := norm_all M N hN h1 x.1 hx hy
    obtain ⟨z, hz, hzx⟩ := descend2 M N Q P hN hP _ (d_sub_d M x.1 hx w) hw
    refine ⟨Submodule.Quotient.mk ⟨z, (memZ _).2 hz⟩, ?_⟩
    rw [H_mk, Submodule.Quotient.eq, Submodule.mem_comap]
    show P.hom.f 2 z - x.1 ∈ M.coch.B 2
    rw [hzx, memB]
    exact ⟨-w, by rw [map_neg]; abel⟩
  · rintro ⟨y0, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y0
    rw [H_mk, H_mk, mk_eq_zero_iff, memB]
    have hinv : ∀ n ∈ N, M.rho n (P.u (cur Q z.1 1 1)) = P.u (cur Q z.1 1 1) := (hP.2.2 _).1 ⟨_, rfl⟩
    refine ⟨mk1 (M.resSub N) (fun _ => P.u (cur Q z.1 1 1)) continuous_const, ?_⟩
    refine ext2 (M.resSub N) fun a b => ?_
    refine (curried_coboundary_eq (M.resSub N) _ continuous_const a b).trans ?_
    have e : cur (M.resSub N) ((Pair.res M N.subtype continuous_subtype_val).hom.Z 2 (P.hom.Z 2 z)).1 a b =
        cur M (P.hom.f 2 z.1) a b := by
      refine congrArg (P.hom.f 2 z.1).1 (funext fun i => ?_)
      fin_cases i <;> rfl
    rw [e, cur_inf M N Q P hP, (QuotientGroup.eq_one_iff _).2 a.2, (QuotientGroup.eq_one_iff _).2 b.2]
    simp only [D1]
    have := hinv a a.2
    have h' : (M.resSub N).rho a (P.u (cur Q z.1 1 1)) = P.u (cur Q z.1 1 1) := this
    rw [h']; abel

end

end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
