import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoHeckeQuotient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeKerModel

open GlobalTheory.HeckeTate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `t.act.add 0 0`. Rewrite `h` using `[add_zero]`. Establish `h1 : t.act.act 0 = 1` using `by simpa using h`.

Simplify using `[h1]`. Consider the case `succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]`.
-/
theorem comp_act_natCast (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
  induction n with
  | zero =>
    have h := t.act.add 0 0
    rw [add_zero] at h
    have h1 : t.act.act 0 = 1 := by simpa using h
    simp [h1]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← comp_act_natCast]`. Conclude with `h _ (Ideal.mem_span_singleton_self _)`. Introduce `h a ha`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton.1 ha`. Use `t.act.hom c` as an intermediate fact. Rewrite using `[t.act.mul, ← Category.assoc, comp_act_natCast, h]`. Simplify using the standard rewrite rules.
-/
theorem mem_tors_span (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ∈ t.tors T (Ideal.span {(n : 𝓞 E)}) ↔ x ^ n = 1 := by
  constructor
  · intro h
    rw [← comp_act_natCast]
    exact h _ (Ideal.mem_span_singleton_self _)
  · intro h a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 ha
    have := t.act.hom c
    rw [t.act.mul, ← Category.assoc, comp_act_natCast, h]
    simp

noncomputable def torsSub (t : SAB H S) (T : Over S) (n : ℕ) : Subgroup (T ⟶ t.G) :=
  { carrier := t.tors T (Ideal.span {(n : 𝓞 E)})
    one_mem' := (mem_tors_span t 1 n).2 (one_pow _)
    mul_mem' := fun {x y} hx hy a ha => by
      have := t.act.hom a
      rw [MonObj.mul_comp, hx a ha, hy a ha, _root_.one_mul]
    inv_mem' := fun {x} hx => (mem_tors_span t _ n).2 (by rw [inv_pow, (mem_tors_span t x n).1 hx, inv_one]) }

/- English proof (translation)
Take `⟨-, I, -⟩` from `o.geom k x β hx`. Establish `hmem : ∀ z, z ∈ torsSub o.t (Over.mk x) p ↔ z ^ p = 1` using `fun z => mem_tors_span o.t z p`. Establish `hset : (torsSub o.t (Over.mk x) p : Set _) = o.t.tors (Over.mk x) (Ideal.span {(p : 𝓞 E)})`. Both sides reduce to the same expression. Establish `hq : 0 < p * p` using `Nat.mul_pos hp hp`.

Use `⟨fun z hz a => ?_, fun J hJ z hz => ?_, fun z hz a ha => ?_, fun z hz w hw => ?_, ?_, ?_⟩` and prove the remaining obligations. Use `o.t.act.hom a` as an intermediate fact. Rewrite `hz`, the goal using `[hmem]`. Rewrite using `[← comp_act_natCast, Category.assoc, ← o.t.act.mul, _root_.mul_comm, o.t.act.mul, ← Category.assoc, comp_act_natCast, hz]`. Simplify using the standard rewrite rules.

Rewrite using `[hset]`. Conclude with `fun a ha => hz a (Ideal.mul_le_left (I := J) (J := P) (by rw [hJ]; exact ha))`. Rewrite `hz` using `[hset]`. Conclude with `hz a (Ideal.mul_le_left ha)`. Take `⟨a, rfl⟩` from `(I.onto p hp z).1 ((hmem z).1 hz)`.

Take `⟨c, rfl⟩` from `(I.onto p hp w).1 ((hmem w).1 hw)`. Establish `h` using `I.isom (p * p) hq (p • a) (p • c)`. Rewrite `h` using `[ev_nsmul, ev_nsmul, I.tower p p hp hp, I.tower p p hp hp]`. Establish `h2 : I.ζ (p * p) ^ D.EF (p • a) (p • c) = 1`. Rewrite using `[((I.ζ_prim _ hq).zpow_eq_one_iff_dvd _)]`.

Use `⟨D.EF a c, ?_⟩` and prove the remaining obligations. Simplify using `only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[h2]`.

Establish `h3 : unitOn (1 : kˣ) = 1` using `map_one _`. Rewrite `h` using `[h3]`. Rewrite using `[sq]`. Conclude with `h` after adjusting the coercions. Use `D.fin` as an intermediate fact.

Use `D.proj` as an intermediate fact. Use `datum_free_int D` as an intermediate fact. Establish `: Module.Finite ℤ D.La` using `Module.Finite.trans (𝓞 E) D.La`. Rewrite using `[← datum_finrank_int, ← AddSubgroup.index_range_nsmul]`. Establish `hker : (evHom I p).ker = (nsmulAddMonoidHom (α` using `D.La) p).range := by`.

Use extensionality with `a`. Conclude with `(I.ker p hp a).trans ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩`. Rewrite using `[← hker, AddSubgroup.index_ker]`. Use `Nat.card_congr ⟨fun z => ⟨Additive.ofMul z.1, ?_⟩, fun z => ⟨z.1.toMul, ?_⟩, fun _ => rfl, fun _ => rfl⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `(I.onto p hp z.1).1 ((hmem _).1 z.2)`.

Conclude with `⟨a, congrArg Additive.ofMul ha⟩`. Take `⟨a, ha⟩` from `z.2`. Conclude with `(hmem _).2 ((I.onto p hp _).2 ⟨a, congrArg Additive.toMul ha⟩)`. Rewrite using `[hset, Set.inter_self, pow_zero, _root_.mul_one]`.
-/
theorem heckeKer_zero {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {s : S ⟶ Sp B}
    (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (hx : x ≫ s = spMap β)
    (P : Ideal (𝓞 E)) (p : ℕ) (hp : 0 < p) :
    o.t.HeckeKer (Over.mk x) D P p 0 (torsSub o.t (Over.mk x) p) := by
  obtain ⟨-, I, -⟩ := o.geom k x β hx
  have hmem : ∀ z, z ∈ torsSub o.t (Over.mk x) p ↔ z ^ p = 1 := fun z => mem_tors_span o.t z p
  have hset : (torsSub o.t (Over.mk x) p : Set _) = o.t.tors (Over.mk x) (Ideal.span {(p : 𝓞 E)}) :=
    rfl
  have hq : 0 < p * p := Nat.mul_pos hp hp
  refine ⟨fun z hz a => ?_, fun J hJ z hz => ?_, fun z hz a ha => ?_, fun z hz w hw => ?_, ?_, ?_⟩
  · have := o.t.act.hom a
    rw [hmem] at hz ⊢
    rw [← comp_act_natCast, Category.assoc, ← o.t.act.mul, _root_.mul_comm, o.t.act.mul, ← Category.assoc,
      comp_act_natCast, hz]
    simp
  · rw [hset]
    exact fun a ha => hz a (Ideal.mul_le_left (I := J) (J := P) (by rw [hJ]; exact ha))
  · rw [hset] at hz
    exact hz a (Ideal.mul_le_left ha)
  · obtain ⟨a, rfl⟩ := (I.onto p hp z).1 ((hmem z).1 hz)
    obtain ⟨c, rfl⟩ := (I.onto p hp w).1 ((hmem w).1 hw)
    have h := I.isom (p * p) hq (p • a) (p • c)
    rw [ev_nsmul, ev_nsmul, I.tower p p hp hp, I.tower p p hp hp] at h
    have h2 : I.ζ (p * p) ^ D.EF (p • a) (p • c) = 1 := by
      rw [((I.ζ_prim _ hq).zpow_eq_one_iff_dvd _)]
      refine ⟨D.EF a c, ?_⟩
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      push_cast
      ring
    rw [h2] at h
    have h3 : unitOn (1 : kˣ) = 1 := map_one _
    rw [h3] at h
    rw [sq]
    exact_mod_cast h
  · have := D.fin
    have := D.proj
    have := datum_free_int D
    have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    rw [← datum_finrank_int, ← AddSubgroup.index_range_nsmul]
    have hker : (evHom I p).ker = (nsmulAddMonoidHom (α := D.La) p).range := by
      ext a
      exact (I.ker p hp a).trans ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
    rw [← hker, AddSubgroup.index_ker]
    refine Nat.card_congr ⟨fun z => ⟨Additive.ofMul z.1, ?_⟩, fun z => ⟨z.1.toMul, ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · obtain ⟨a, ha⟩ := (I.onto p hp z.1).1 ((hmem _).1 z.2)
      exact ⟨a, congrArg Additive.ofMul ha⟩
    · obtain ⟨a, ha⟩ := z.2
      exact (hmem _).2 ((I.onto p hp _).2 ⟨a, congrArg Additive.toMul ha⟩)
  · rw [hset, Set.inter_self, pow_zero, _root_.mul_one]

end GlobalTheory.HeckeKerModel
