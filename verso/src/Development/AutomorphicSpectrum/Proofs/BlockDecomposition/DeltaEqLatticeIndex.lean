import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

/- English proof (translation)
Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) (Finset.univ : Finset (Fin m × Fin m)) (fun p => c p.1 p.2)`. Establish `hb0 : (b : 𝓞 K) ≠ 0` using `nonZeroDivisors.ne_zero b.2`. Use `choose r hr using fun (i j : Fin m) => RingHom.mem_rangeS.1 (hb (i, j) (Finset.mem_univ _))`. Establish `hr' : ∀ i j, algebraMap (𝓞 K) K (r i j) = algebraMap (𝓞 K) K (b : 𝓞 K) * c i j`. Introduce `i j`.

Rewrite using `[hr i j, Algebra.smul_def]`. Set `I : Ideal (𝓞 K)` to `Ideal.span {(b : 𝓞 K)}`. Establish `hI : I ≠ ⊥` using `fun h => hb0 (Ideal.span_singleton_eq_bot.1 h)`. Use `haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI`. Set `π : (Fin m → 𝓞 K) →+ (Fin m → 𝓞 K ⧸ I)` to `AddMonoidHom.pi (fun i => (Ideal.Quotient.mk I).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ : Fin m => 𝓞 K) i))`.

Establish `hker : π.ker ≤ Kc c`. Introduce `y hy`. Establish `h0 : π y = 0` using `AddMonoidHom.mem_ker.1 hy`. Establish `hyI : ∀ j, y j ∈ I` using `fun j => Ideal.Quotient.eq_zero_iff_mem.1 (congrFun h0 j)`. Use `choose z hz using fun j => Ideal.mem_span_singleton'.1 (hyI j)`.

Express the relevant statement in the definitionally equal form `∀ i : Fin m, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = c.mulVec (fun j => algebraMap (𝓞 K) K (y j)) i`. Introduce `i`. Use `⟨∑ j, r i j * z j, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hr' i j, ← hz j, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hfin : (π.ker).index ≠ 0`. Rewrite using `[AddSubgroup.index_ker]`.

Conclude with `Nat.card_pos.ne'`. Conclude with `ne_zero_of_dvd_ne_zero hfin (AddSubgroup.index_dvd_of_le hker)`.
-/
theorem delta_ne_zero (c : Matrix (Fin m) (Fin m) K) : delta c ≠ 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K))
    (Finset.univ : Finset (Fin m × Fin m)) (fun p => c p.1 p.2)
  have hb0 : (b : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero b.2
  choose r hr using fun (i j : Fin m) => RingHom.mem_rangeS.1 (hb (i, j) (Finset.mem_univ _))
  have hr' : ∀ i j, algebraMap (𝓞 K) K (r i j) = algebraMap (𝓞 K) K (b : 𝓞 K) * c i j := by
    intro i j
    rw [hr i j, Algebra.smul_def]
  let I : Ideal (𝓞 K) := Ideal.span {(b : 𝓞 K)}
  have hI : I ≠ ⊥ := fun h => hb0 (Ideal.span_singleton_eq_bot.1 h)
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let π : (Fin m → 𝓞 K) →+ (Fin m → 𝓞 K ⧸ I) :=
    AddMonoidHom.pi (fun i => (Ideal.Quotient.mk I).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun _ : Fin m => 𝓞 K) i))
  have hker : π.ker ≤ Kc c := by
    intro y hy
    have h0 : π y = 0 := AddMonoidHom.mem_ker.1 hy
    have hyI : ∀ j, y j ∈ I := fun j =>
      Ideal.Quotient.eq_zero_iff_mem.1 (congrFun h0 j)
    choose z hz using fun j => Ideal.mem_span_singleton'.1 (hyI j)
    change ∀ i : Fin m, ∃ o : 𝓞 K,
      algebraMap (𝓞 K) K o = c.mulVec (fun j => algebraMap (𝓞 K) K (y j)) i
    intro i
    refine ⟨∑ j, r i j * z j, ?_⟩
    rw [map_sum]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, hr' i j, ← hz j, map_mul]
    ring
  have hfin : (π.ker).index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos.ne'
  exact ne_zero_of_dvd_ne_zero hfin (AddSubgroup.index_dvd_of_le hker)

/- English proof (translation)
Set `L` to `(lam c).toAddSubgroup`. Set `H : AddSubgroup L` to `(intVec K m).toAddSubgroup.addSubgroupOf L`. Set `f0 : (Fin m → 𝓞 K) →+ (Fin m → K)` to `(c.mulVecLin.toAddMonoidHom).comp (AddMonoidHom.pi fun i => (algebraMap (𝓞 K) K).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ : Fin m => 𝓞 K) i))`. Establish `hmap : ∀ y, f0 y ∈ L`. Introduce `y`.

Establish `: f0 y ∈ lam c`. Unfold `lam`. Use `Submodule.mem_sup_right (Submodule.mem_map.2 ⟨fun j => algebraMap (𝓞 K) K (y j), fun j => ⟨y j, rfl⟩, rfl⟩)` and prove the remaining obligations. Conclude with `this`. Set `ψ : (Fin m → 𝓞 K) →+ L` to `f0.codRestrict L hmap`.

Set `φ : (Fin m → 𝓞 K) →+ L ⧸ H` to `(QuotientAddGroup.mk' H).comp ψ`. Establish `hker : Kc c = φ.ker`. Use extensionality with `y`. Rewrite using `[AddMonoidHom.mem_ker]`. Express the relevant statement in the definitionally equal form `_ ↔ (QuotientAddGroup.mk (ψ y) : L ⧸ H) = 0`.

Rewrite using `[QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`. Both sides reduce to the same expression. Establish `hsurj : Function.Surjective φ`. Introduce `q`. Proceed by induction on `q using QuotientAddGroup.induction_on with`.

Consider the case `H x`. Take `⟨x, hx⟩` from `x`. Establish `hx' : x ∈ lam c` using `hx`. Unfold `lam at hx'`. Take `⟨a, ha, w, hw, rfl⟩` from `Submodule.mem_sup.1 hx'`.

Take `⟨v, hv, rfl⟩` from `Submodule.mem_map.1 hw`. Use `choose y hy using hv`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `hyv : (fun j => algebraMap (𝓞 K) K (y j)) = v` using `funext hy`. Express the relevant statement in the definitionally equal form `(QuotientAddGroup.mk (ψ y) : L ⧸ H) = QuotientAddGroup.mk _`.

Rewrite using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Establish `key : ((-(ψ y) + ⟨_, hx⟩ : L) : Fin m → K) = a`. Rewrite using `[AddSubgroup.coe_add, AddSubgroup.coe_neg]`. Express the relevant statement in the definitionally equal form `-(c.mulVec (fun j => algebraMap (𝓞 K) K (y j))) + (a + c.mulVec v) = a`. Rewrite using `[hyv]`.

Normalize the expressions using the abelian group laws. Rewrite using `[key]`. Conclude with `ha`. Use `show (Kc c).index = H.index`. Rewrite using `[hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top]`.

Both sides reduce to the same expression.
-/
theorem delta_eq_relIndex (c : Matrix (Fin m) (Fin m) K) :
    delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  classical
  let L := (lam c).toAddSubgroup
  let H : AddSubgroup L := (intVec K m).toAddSubgroup.addSubgroupOf L
  let f0 : (Fin m → 𝓞 K) →+ (Fin m → K) :=
    (c.mulVecLin.toAddMonoidHom).comp (AddMonoidHom.pi fun i =>
      (algebraMap (𝓞 K) K).toAddMonoidHom.comp (Pi.evalAddMonoidHom (fun _ : Fin m => 𝓞 K) i))
  have hmap : ∀ y, f0 y ∈ L := by
    intro y
    have : f0 y ∈ lam c := by
      unfold lam
      refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨fun j => algebraMap (𝓞 K) K (y j),
        fun j => ⟨y j, rfl⟩, rfl⟩)
    exact this
  let ψ : (Fin m → 𝓞 K) →+ L := f0.codRestrict L hmap
  let φ : (Fin m → 𝓞 K) →+ L ⧸ H := (QuotientAddGroup.mk' H).comp ψ
  have hker : Kc c = φ.ker := by
    ext y
    rw [AddMonoidHom.mem_ker]
    change _ ↔ (QuotientAddGroup.mk (ψ y) : L ⧸ H) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rfl
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨x, hx⟩ := x
      have hx' : x ∈ lam c := hx
      unfold lam at hx'
      obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
      choose y hy using hv
      refine ⟨y, ?_⟩
      have hyv : (fun j => algebraMap (𝓞 K) K (y j)) = v := funext hy
      change (QuotientAddGroup.mk (ψ y) : L ⧸ H) = QuotientAddGroup.mk _
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have key : ((-(ψ y) + ⟨_, hx⟩ : L) : Fin m → K) = a := by
        rw [AddSubgroup.coe_add, AddSubgroup.coe_neg]
        change -(c.mulVec (fun j => algebraMap (𝓞 K) K (y j))) + (a + c.mulVec v) = a
        rw [hyv]
        abel
      rw [key]
      exact ha
  show (Kc c).index = H.index
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top]
  rfl

/- English proof (translation)
Introduce `K _ _ m c`. Conclude with `⟨delta_ne_zero c, delta_eq_relIndex c⟩`.
-/
theorem delta_index : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ)
    (c : Matrix (Fin m) (Fin m) K),
    delta c ≠ 0 ∧ delta c = (intVec K m).toAddSubgroup.relIndex (lam c).toAddSubgroup := by
  intro K _ _ m c
  exact ⟨delta_ne_zero c, delta_eq_relIndex c⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DeltaIndex
