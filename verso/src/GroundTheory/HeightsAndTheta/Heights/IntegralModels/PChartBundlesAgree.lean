import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PAwayHeightOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Introduce `v hv`. Set `A` to `chartRing o x i`. Set `J : Ideal A` to `{ carrier := {a | (a : Ω) • v ∈ B'.lat i} add_mem' := fun {a b} ha hb => by`. Express the relevant statement in the definitionally equal form `((a + b : A) : Ω) • v ∈ B'.lat i`. Rewrite using `[Subalgebra.coe_add, add_smul]`.

Conclude with `add_mem ha hb`. Use the proof step `zero_mem' := by`. Express the relevant statement in the definitionally equal form `((0 : A) : Ω) • v ∈ B'.lat i`. Rewrite using `[Subalgebra.coe_zero, zero_smul]`. Conclude with `zero_mem _`.

Use the proof step `smul_mem' := fun c a ha => by`. Express the relevant statement in the definitionally equal form `((c * a : A) : Ω) • v ∈ B'.lat i`. Rewrite using `[Subalgebra.coe_mul, mul_smul]`. Conclude with `B'.stable i c c.2 _ ha }`. Establish `hJ : ∀ a : A, a ∈ J ↔ (a : Ω) • v ∈ B'.lat i` using `fun _ => Iff.rfl`.

Take `⟨k, f, c, hf, hc, hsum, hb⟩` from `B'.frame i hi`. Establish `hfJ : ∀ l, (⟨f l, hf l⟩ : A) ∈ J.radical`. Introduce `l`. Take `⟨b, hli, hsp, hiff⟩` from `hb l`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n : ℕ, f l ^ n • v ∈ B'.lat i := by`.

Distinguish the cases in `hf0 : f l = 0`. Conclude with `⟨1, by rw [hf0, pow_one, zero_smul]; exact zero_mem _⟩`. Set `bs` to `Module.Basis.mk hli (by rw [hsp])`. Establish `hbs : ∀ q, bs q = b q` using `fun q => Module.Basis.mk_apply hli _ q`. Set `a` to `bs.equivFun v`.

Establish `coord : ∀ t : A, (t : Ω) • v ∈ B'.lat i → ∀ q, ∃ n : ℕ, f l ^ n * ((t : Ω) * a q) ∈ A`. Introduce `t ht q`. Take `⟨a', ha', he⟩` from `(hiff ((t : Ω) • v)).1 ⟨0, by rw [pow_zero, one_smul]; exact ht⟩`. Establish `e1 : bs.equivFun ((t : Ω) • v) = a'`. Rewrite using `[he]`.

Repeatedly rewrite using `[← hbs]`. Rewrite using `[← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]`. Establish `e2 : a' q = (t : Ω) * a q`. Rewrite using `[← e1, LinearEquiv.map_smul]`. Both sides reduce to the same expression.

Rewrite using `[← e2]`. Conclude with `ha' q`. Use `(hiff v).2 ⟨a, fun q => ?_, ?_⟩` and prove the remaining obligations. Establish `hh : (⟨f l, hf l⟩ : A) ≠ 0` using `fun e => hf0 (congrArg Subtype.val e)`. Take `⟨m, g, hg⟩` from `mem_away_of_heightOne hHOI A Ω Subtype.val_injective ⟨f l, hf l⟩ hh (a q) (by`.

Take `⟨s, hs0, hs⟩` from `h1 v hv`. Take `⟨n, hn⟩` from `coord s hs q`. Use `⟨s, hs0, n, ⟨_, hn⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f l ^ n * (s : Ω) * a q = f l ^ n * ((s : Ω) * a q)`. Use the proof step `ring)`.

Use the proof step `(fun P hP hP1 _ => by`. Establish `hv1 : ∃ s : A, s ∉ P ∧ (s : Ω) • v ∈ B.lat i` using `⟨1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h), by`. Rewrite using `[OneMemClass.coe_one, one_smul]`. Conclude with `hv⟩`. Take `⟨t, htP, ht⟩` from `hq P hP hP1 v hv1`.

Take `⟨n, hn⟩` from `coord t ht q`. Use `⟨t, htP, n, ⟨_, hn⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f l ^ n * (t : Ω) * a q = f l ^ n * ((t : Ω) * a q)`. Use the proof step `ring)`. Use `⟨m, ?_⟩` and prove the remaining obligations.

Establish `hg' : f l ^ m * a q = (g : Ω)` using `hg`. Rewrite using `[hg']`. Conclude with `g.2`. Rewrite using `[← bs.sum_equivFun v]`. Repeatedly rewrite using `[hbs]`.

Both sides reduce to the same expression. Conclude with `⟨n, (hJ _).2 (by rw [SubmonoidClass.coe_pow]; exact hn)⟩`. Establish `h1J : (1 : A) ∈ J.radical`. Establish `e : (1 : A) = ∑ l, (⟨c l, hc l⟩ : A) * ⟨f l, hf l⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[OneMemClass.coe_one, ← hsum, AddSubmonoidClass.coe_finsetSum]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hfJ l)`. Establish `hJtop : J = ⊤` using `Ideal.radical_eq_top.1 ((Ideal.eq_top_iff_one _).2 h1J)`.

Establish `h1 : (1 : A) ∈ J` using `hJtop ▸ Submodule.mem_top`. Establish `h1'` using `(hJ 1).1 h1`. Rewrite `h1'` using `[OneMemClass.coe_one, one_smul]`. Then use the resulting hypothesis.
-/
theorem ChartBundlesAgree.lat_le (hHOI : HeightOneIntersection.Statement)
    {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] (B B' : ChartBundle o x r E) (i : τ) (hi : x i ≠ 0)
    (hN : IsNoetherianRing (chartRing o x i)) (hIC : IsIntegrallyClosed (chartRing o x i))
    (h1 : ∀ v ∈ B.lat i, ∃ s : chartRing o x i, s ≠ 0 ∧ (s : Ω) • v ∈ B'.lat i)
    (hq : ∀ q : Ideal (chartRing o x i), q.IsPrime → q.height = 1 → ∀ v : E,
      (∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B.lat i) →
        ∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B'.lat i) :
    B.lat i ≤ B'.lat i := by
  intro v hv
  let A := chartRing o x i
  let J : Ideal A :=
    { carrier := {a | (a : Ω) • v ∈ B'.lat i}
      add_mem' := fun {a b} ha hb => by
        change ((a + b : A) : Ω) • v ∈ B'.lat i
        rw [Subalgebra.coe_add, add_smul]
        exact add_mem ha hb
      zero_mem' := by
        change ((0 : A) : Ω) • v ∈ B'.lat i
        rw [Subalgebra.coe_zero, zero_smul]
        exact zero_mem _
      smul_mem' := fun c a ha => by
        change ((c * a : A) : Ω) • v ∈ B'.lat i
        rw [Subalgebra.coe_mul, mul_smul]
        exact B'.stable i c c.2 _ ha }
  have hJ : ∀ a : A, a ∈ J ↔ (a : Ω) • v ∈ B'.lat i := fun _ => Iff.rfl
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := B'.frame i hi
  have hfJ : ∀ l, (⟨f l, hf l⟩ : A) ∈ J.radical := by
    intro l
    obtain ⟨b, hli, hsp, hiff⟩ := hb l
    obtain ⟨n, hn⟩ : ∃ n : ℕ, f l ^ n • v ∈ B'.lat i := by
      by_cases hf0 : f l = 0
      · exact ⟨1, by rw [hf0, pow_one, zero_smul]; exact zero_mem _⟩
      · let bs := Module.Basis.mk hli (by rw [hsp])
        have hbs : ∀ q, bs q = b q := fun q => Module.Basis.mk_apply hli _ q
        let a := bs.equivFun v

        have coord : ∀ t : A, (t : Ω) • v ∈ B'.lat i →
            ∀ q, ∃ n : ℕ, f l ^ n * ((t : Ω) * a q) ∈ A := by
          intro t ht q
          obtain ⟨a', ha', he⟩ := (hiff ((t : Ω) • v)).1 ⟨0, by rw [pow_zero, one_smul]; exact ht⟩
          have e1 : bs.equivFun ((t : Ω) • v) = a' := by
            rw [he]
            simp_rw [← hbs]
            rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
          have e2 : a' q = (t : Ω) * a q := by
            rw [← e1, LinearEquiv.map_smul]
            rfl
          rw [← e2]
          exact ha' q
        refine (hiff v).2 ⟨a, fun q => ?_, ?_⟩
        · have hh : (⟨f l, hf l⟩ : A) ≠ 0 := fun e => hf0 (congrArg Subtype.val e)
          obtain ⟨m, g, hg⟩ := mem_away_of_heightOne hHOI A Ω Subtype.val_injective
            ⟨f l, hf l⟩ hh (a q)
            (by
              obtain ⟨s, hs0, hs⟩ := h1 v hv
              obtain ⟨n, hn⟩ := coord s hs q
              refine ⟨s, hs0, n, ⟨_, hn⟩, ?_⟩
              change f l ^ n * (s : Ω) * a q = f l ^ n * ((s : Ω) * a q)
              ring)
            (fun P hP hP1 _ => by
              have hv1 : ∃ s : A, s ∉ P ∧ (s : Ω) • v ∈ B.lat i :=
                ⟨1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h), by
                  rw [OneMemClass.coe_one, one_smul]; exact hv⟩
              obtain ⟨t, htP, ht⟩ := hq P hP hP1 v hv1
              obtain ⟨n, hn⟩ := coord t ht q
              refine ⟨t, htP, n, ⟨_, hn⟩, ?_⟩
              change f l ^ n * (t : Ω) * a q = f l ^ n * ((t : Ω) * a q)
              ring)
          refine ⟨m, ?_⟩
          have hg' : f l ^ m * a q = (g : Ω) := hg
          rw [hg']
          exact g.2
        · rw [← bs.sum_equivFun v]
          simp_rw [hbs]
          rfl
    exact ⟨n, (hJ _).2 (by rw [SubmonoidClass.coe_pow]; exact hn)⟩
  have h1J : (1 : A) ∈ J.radical := by
    have e : (1 : A) = ∑ l, (⟨c l, hc l⟩ : A) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      rw [OneMemClass.coe_one, ← hsum, AddSubmonoidClass.coe_finsetSum]
      rfl
    rw [e]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hfJ l)
  have hJtop : J = ⊤ := Ideal.radical_eq_top.1 ((Ideal.eq_top_iff_one _).2 h1J)
  have h1 : (1 : A) ∈ J := hJtop ▸ Submodule.mem_top
  have h1' := (hJ 1).1 h1
  rwa [OneMemClass.coe_one, one_smul] at h1'

/- English proof (translation)
Introduce `o _ Ω _ _ τ x r E _ _ B B' i hi hN hIC h1 h2 hq`. Conclude with `le_antisymm (ChartBundlesAgree.lat_le hHOI B B' i hi hN hIC h1 fun q hq' hq1 v => (hq q hq' hq1 v).1) (ChartBundlesAgree.lat_le hHOI B' B i hi hN hIC h2 fun q hq' hq1 v => (hq q hq' hq1 v).2)`.
-/
theorem ChartBundlesAgree.proof (hHOI : HeightOneIntersection.Statement) :
    ChartBundlesAgree.Statement := by
  intro o _ Ω _ _ τ x r E _ _ B B' i hi hN hIC h1 h2 hq
  exact le_antisymm
    (ChartBundlesAgree.lat_le hHOI B B' i hi hN hIC h1 fun q hq' hq1 v => (hq q hq' hq1 v).1)
    (ChartBundlesAgree.lat_le hHOI B' B i hi hN hIC h2 fun q hq' hq1 v => (hq q hq' hq1 v).2)

end

end GroundTheory.Heights₂.Heights.Model
