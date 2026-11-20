import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspCell

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.DiagCell

set_option synthInstance.maxHeartbeats 400000

/- English proof (translation)
Establish `hc : ∑ j, Multiset.card (t j) = 1`. Use `congrArg Multiset.card h` as an intermediate fact. Rewrite `this` using `[Multiset.card_sum]`. Simplify using `using this.symm`. Take `⟨j₀, -, h1⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (hc.symm ▸ one_ne_zero)`.

Establish `hz : ∀ j, j ≠ j₀ → t j = 0` using `fun j hj => by`. Establish `h2` using `Finset.add_le_sum (s := Finset.univ) (f := fun j => Multiset.card (t j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j₀) (Finset.mem_univ j) (Ne.symm hj)`. Simplify using `only [hc] at h2`. Conclude with `Multiset.card_eq_zero.1 (by omega)`. Use `⟨j₀, ?_, hz⟩` and prove the remaining obligations.

Rewrite using `[h, Finset.sum_eq_single j₀ (fun j _ hj => hz j hj) (by simp)]`.
-/
theorem exists_eq_singleton_of_sum {ι A : Type*} [Fintype ι] [DecidableEq ι] {a : A} {t : ι → Multiset A}
    (h : ({a} : Multiset A) = ∑ j, t j) : ∃ j₀, t j₀ = {a} ∧ ∀ j, j ≠ j₀ → t j = 0 := by
  have hc : ∑ j, Multiset.card (t j) = 1 := by
    have := congrArg Multiset.card h
    rw [Multiset.card_sum] at this
    simpa using this.symm
  obtain ⟨j₀, -, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hc.symm ▸ one_ne_zero)
  have hz : ∀ j, j ≠ j₀ → t j = 0 := fun j hj => by
    have h2 := Finset.add_le_sum (s := Finset.univ) (f := fun j => Multiset.card (t j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j₀) (Finset.mem_univ j) (Ne.symm hj)
    simp only [hc] at h2
    exact Multiset.card_eq_zero.1 (by omega)
  refine ⟨j₀, ?_, hz⟩
  rw [h, Finset.sum_eq_single j₀ (fun j _ hj => hz j hj) (by simp)]

/- English proof (translation)
Use `choose r hr1 hr0 using fun i => exists_eq_singleton_of_sum (hr i)`. Use `choose e he1 he0 using fun j => exists_eq_singleton_of_sum (hc j)`. Establish `hne : ∀ {a : A}, ({a} : Multiset A) ≠ 0` using `Multiset.singleton_ne_zero _`. Establish `h1 : ∀ i, e (r i) = i` using `fun i => by`. Assume the negation of the conclusion as `hi`.

Conclude with `hne ((hr1 i).symm.trans (he0 (r i) i (Ne.symm hi)))`. Establish `h2 : ∀ j, r (e j) = j` using `fun j => by`. Assume the negation of the conclusion as `hj`. Conclude with `hne ((he1 j).symm.trans (hr0 (e j) j (Ne.symm hj)))`. Use `⟨⟨e, r, h2, h1⟩, fun a => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Establish `h3` using `hr1 (e a)`. Rewrite `h3` using `[h2 a, he1 a]`. Conclude with `Multiset.singleton_inj.1 h3`. Distinguish the cases in `h : e j = i`. Substitute `h` using the available equality.

Establish `h3` using `hr1 (e j)`. Rewrite `h3` using `[h2 j]`. Simplify using `using h3`. Simplify `he0 j i (Ne.symm h)` using `[h]`.
-/
theorem exists_equiv_of_sums {l c : ℕ} {A : Type*} {x : Fin l → A} {y : Fin c → A} {t : Fin l → Fin c → Multiset A}
    (hr : ∀ i, ({x i} : Multiset A) = ∑ j, t i j) (hc : ∀ j, ({y j} : Multiset A) = ∑ i, t i j) :
    ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, t i j = if e j = i then {x i} else 0 := by
  choose r hr1 hr0 using fun i => exists_eq_singleton_of_sum (hr i)
  choose e he1 he0 using fun j => exists_eq_singleton_of_sum (hc j)
  have hne : ∀ {a : A}, ({a} : Multiset A) ≠ 0 := Multiset.singleton_ne_zero _
  have h1 : ∀ i, e (r i) = i := fun i => by
    by_contra hi
    exact hne ((hr1 i).symm.trans (he0 (r i) i (Ne.symm hi)))
  have h2 : ∀ j, r (e j) = j := fun j => by
    by_contra hj
    exact hne ((he1 j).symm.trans (hr0 (e j) j (Ne.symm hj)))
  refine ⟨⟨e, r, h2, h1⟩, fun a => ?_, fun i j => ?_⟩
  · have h3 := hr1 (e a)
    rw [h2 a, he1 a] at h3
    exact Multiset.singleton_inj.1 h3
  · by_cases h : e j = i
    · subst h
      have h3 := hr1 (e j)
      rw [h2 j] at h3
      simpa using h3
    · simpa [h] using he0 j i (Ne.symm h)

/- English proof (translation)
Establish `hG` using `GlobalTheory.CompanionTheory.GeoLink.geometricLemma`. Establish `hBZ` using `GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness`. Establish `hτ : (piTensor fun j => (y j).rep).IsIrreducible` using `GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (y j).2.rep`. Establish `hτs : IsSmooth (piTensor fun j => (y j).rep)` using `isSmooth_piTensor fun j => (y j).2.rep.smooth`. Take `⟨s, hrow, hcol⟩` from `GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (hG k).2 f g (fun i => (x i).2.rep.smooth) (fun i => (x i).2.rep.hasFiniteLength) hτ hτs h0`.

Establish `hR : ∀ i, ∃ t : Fin c → Multiset (IrrGL k), (∀ j, HasSupport (s i j).ρ (t j)) ∧ {x i} = ∑ j, t j` using `fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_sum_of_jac hG hBZ (hasSupport_self (hxc i)) (f i) (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => s i j) (hrow i) (fun j => s i j) (fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD …`. Use `choose t ht hAt using hR`. Establish `hC : ∀ j, HasSupport (y j).rep (∑ i, t i j)`. Introduce `j`. Establish `hd : ∑ i, b.1 i j = (y j).1` using `by simpa using Fintype.card_congr (g j)`.

Establish `hy` using `GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j`. Establish `h1` using `isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).ρ) j (y j).2.rep.irr (hy.trans (isSubquotient_comp hcol _))`. Take `⟨φ⟩` from `(GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1 (piTensor fun i => (s i j).ρ)`. Set `ψ` to `φ.trans (prodIrrEquiv hd (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr)`. Conclude with `GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (y := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr) (fun i => (ht i j).of_equiv (IrrGL.equivOf _ _ _)) (y j).2.rep.irr (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective) …`.

Establish `hU : ∀ j, ({y j} : Multiset (IrrGL k)) = ∑ i, t i j` using `fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ (hasSupport_self (hyc j)) (hC j)`. Take `⟨e, he, het⟩` from `exists_equiv_of_sums hAt hU`. Use `⟨e, he, fun i j => ?_⟩` and prove the remaining obligations. Establish `hd` using `(ht i j).sum_fst`. Rewrite `hd` using `[het i j]`.

Apply the tactic sequence `split_ifs at hd ⊢ <;> simpa using hd.symm`.
-/
theorem exists_equiv_of_jhMult_cell_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k)
    (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp)
    (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1)
    (h0 : jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) ≠ 0) :
    ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, b.1 i j = if e j = i then (x i).1 else 0 := by
  have hG := GlobalTheory.CompanionTheory.GeoLink.geometricLemma
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (y j).2.rep
  have hτs : IsSmooth (piTensor fun j => (y j).rep) := isSmooth_piTensor fun j => (y j).2.rep.smooth
  obtain ⟨s, hrow, hcol⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (hG k).2 f g (fun i => (x i).2.rep.smooth)
    (fun i => (x i).2.rep.hasFiniteLength) hτ hτs h0
  have hR : ∀ i, ∃ t : Fin c → Multiset (IrrGL k), (∀ j, HasSupport (s i j).ρ (t j)) ∧ {x i} = ∑ j, t j :=
    fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_sum_of_jac hG hBZ (hasSupport_self (hxc i)) (f i)
      (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => s i j) (hrow i)
      (fun j => s i j) (fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle _ (fun j => (s i j).irr) j)
  choose t ht hAt using hR
  have hC : ∀ j, HasSupport (y j).rep (∑ i, t i j) := by
    intro j
    have hd : ∑ i, b.1 i j = (y j).1 := by simpa using Fintype.card_congr (g j)
    have hy := GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).ρ) j (y j).2.rep.irr
      (hy.trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (s i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr)
    exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr)
      (fun i => (ht i j).of_equiv (IrrGL.equivOf _ _ _)) (y j).2.rep.irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  have hU : ∀ j, ({y j} : Multiset (IrrGL k)) = ∑ i, t i j :=
    fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ (hasSupport_self (hyc j)) (hC j)
  obtain ⟨e, he, het⟩ := exists_equiv_of_sums hAt hU
  refine ⟨e, he, fun i j => ?_⟩
  have hd := (ht i j).sum_fst
  rw [het i j] at hd
  split_ifs at hd ⊢ <;> simpa using hd.symm

end GlobalTheory.CompanionTheory.CuspCell
